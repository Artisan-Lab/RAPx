#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
use crate::rap_info;

use super::{domain::*, range::RangeType, range::*};
// use rand::Rng;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::*;

use rustc_abi::FieldIdx;

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt::Debug,
};
pub struct ConstraintGraph<'tcx, T: IntervalArithmetic + Debug> {
    // Protected fields
    pub vars: VarNodes<'tcx, T>, // The variables of the source program
    pub oprs: GenOprs<'tcx, T>,  // The operations of the source program

    // func: Option<Function>,             // Save the last Function analyzed
    pub defmap: DefMap<'tcx>, // Map from variables to the operations that define them
    pub usemap: UseMap<'tcx>, // Map from variables to operations where variables are used
    pub symbmap: SymbMap<'tcx>, // Map from variables to operations where they appear as bounds
    pub values_branchmap: ValuesBranchMap<'tcx, T>, // Store intervals, basic blocks, and branches
    // values_switchmap: ValuesSwitchMap<'tcx, T>, // Store intervals for switch branches
    constant_vector: Vec<T>, // Vector for constants from an SCC

    pub inst_rand_place_set: Vec<Place<'tcx>>,
    pub essa: DefId,
    pub ssa: DefId,

    pub index: i32,
    pub dfs: HashMap<&'tcx Place<'tcx>, i32>,
    pub root: HashMap<&'tcx Place<'tcx>, &'tcx Place<'tcx>>,
    pub in_component: HashSet<&'tcx Place<'tcx>>,
    pub components: HashMap<&'tcx Place<'tcx>, HashSet<&'tcx Place<'tcx>>>,
    pub worklist: VecDeque<&'tcx Place<'tcx>>,
    pub numAloneSCCs: usize,
    pub numSCCs: usize, // Add a stub for pre_update to resolve the missing method error.
}

impl<'tcx, T> ConstraintGraph<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn convert_const(c: &Const) -> Option<T> {
        T::from_const(c)
    }

    pub fn new(essa: DefId, ssa: DefId) -> Self {
        Self {
            vars: VarNodes::new(),
            oprs: GenOprs::new(),
            // func: None,
            defmap: DefMap::new(),
            usemap: UseMap::new(),
            symbmap: SymbMap::new(),
            values_branchmap: ValuesBranchMap::new(),
            // values_switchmap: ValuesSwitchMap::new(),
            constant_vector: Vec::new(),
            inst_rand_place_set: Vec::new(),
            essa,
            ssa,
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: VecDeque::new(),
            numAloneSCCs: 0,
            numSCCs: 0, // oprs:oprs
        }
    }
    pub fn print_vars(&self) {
        for (&key, value) in &self.vars {
            rap_info!("var: {:?}. {:?}\n ", key, value.get_range());
        }
    }
    fn print_values_branchmap(&self) {
        for (key, value) in &self.values_branchmap {
            rap_info!("vbm place: {:?}. {:?}\n ", key, value);
        }
    }
    fn print_defmap(&self) {
        for (key, value) in self.defmap.clone() {
            rap_info!(
                "place: {:?} def in stmt:{:?} {:?}",
                key,
                self.oprs[value].get_type_name(),
                self.oprs[value].get_instruction()
            );
        }
    }
    fn print_compusemap(
        &self,
        component: &HashSet<&'tcx Place<'tcx>>,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
    ) {
        for (key, value) in comp_use_map.clone() {
            if component.contains(key) {
                for v in value {
                    rap_info!(
                        "place: {:?} use in stmt:{:?} {:?}",
                        key,
                        self.oprs[v].get_type_name(),
                        self.oprs[v].get_instruction()
                    );
                }
            }
        }
    }
    fn print_usemap(&self) {
        for (key, value) in self.usemap.clone() {
            for v in value {
                rap_info!(
                    "place: {:?} use in stmt:{:?} {:?}",
                    key,
                    self.oprs[v].get_type_name(),
                    self.oprs[v].get_instruction()
                );
            }
        }
    }
    // pub fn create_random_place(&mut self) -> Place<'tcx> {
    //     let mut rng = rand::rng();
    //     let random_local = Local::from_usize(rng.random_range(10000..100000));
    //     let place = Place {
    //         local: random_local,
    //         projection: ty::List::empty(),
    //     };
    //     self.inst_rand_place_set.push(place);
    //     place
    // }
    pub fn add_varnode(&mut self, v: &'tcx Place<'tcx>) -> &mut VarNode<'tcx, T> {
        let node = VarNode::new(v);
        let node_ref: &mut VarNode<'tcx, T> = self.vars.entry(v).or_insert(node);
        self.usemap.entry(v).or_insert(HashSet::new());

        node_ref
    }

    pub fn build_graph(&mut self, body: &'tcx Body<'tcx>) {
        // print!("====Building graph====\n");
        // self.build_value_maps(body);
        // print!("varnodes{:?}\n", self.vars);
        // self.print_values_branchmap();
        // print!("====build_operations====\n");

        for block in body.basic_blocks.indices() {
            let block_data = &body[block];
            // Traverse statements

            for statement in block_data.statements.iter() {
                self.build_operations(statement, block);
            }
        }

        // print!("len {:?} varnodes{:?}\n", self.vars.len(), self.vars);
        // print!("len {:?} oprs{:?}\n", self.oprs.len(), self.oprs);
        // self.print_defmap();
        // self.print_usemap();
        // print!("end\n");
    }

    pub fn build_value_maps(&mut self, body: &'tcx Body<'tcx>) {
        for bb in body.basic_blocks.indices() {
            let block_data = &body[bb];
            if let Some(terminator) = &block_data.terminator {
                match &terminator.kind {
                    TerminatorKind::SwitchInt { discr, targets } => {
                        // print!("SwitchIntblock{:?}\n", bb);
                        self.build_value_branch_map(body, discr, targets, block_data);
                    }
                    TerminatorKind::Goto { target } => {
                        // self.build_value_goto_map(block_index, *target);
                    }
                    _ => {
                        // print!(
                        //     "BasicBlock {:?} has an unsupported terminator: {:?}",
                        //     block_index, terminator.kind
                        // );
                    }
                }
            }
        }
        // print!("value_branchmap{:?}\n", self.values_branchmap);
        // print!("varnodes{:?}\n,", self.vars);
    }

    pub fn build_value_branch_map(
        &mut self,
        body: &Body<'tcx>,
        discr: &'tcx Operand<'tcx>,
        targets: &'tcx SwitchTargets,
        block: &'tcx BasicBlockData<'tcx>,
    ) {
        // let place1: &Place<'tcx>;

        if let Operand::Copy(place) | Operand::Move(place) = discr {
            if let Some((op1, op2, cmp_op)) = self.extract_condition(place, block) {
                let const_op1 = op1.constant();
                let const_op2 = op2.constant();

                match (const_op1, const_op2) {
                    (Some(c1), Some(c2)) => {}
                    (Some(c), None) | (None, Some(c)) => {
                        let const_in_left: bool;
                        let variable;
                        if const_op1.is_some() {
                            const_in_left = true;
                            variable = match op2 {
                                Operand::Copy(p) | Operand::Move(p) => p,
                                _ => panic!("Expected a place"),
                            };
                        } else {
                            const_in_left = false;
                            variable = match op1 {
                                Operand::Copy(p) | Operand::Move(p) => p,
                                _ => panic!("Expected a place"),
                            };
                        }
                        self.add_varnode(variable);
                        // print!("add_vbm_varnode{:?}\n", variable.clone());

                        // let value = c.const_.try_to_scalar_int().unwrap();
                        let value = Self::convert_const(&c.const_).unwrap();
                        let const_range =
                            Range::new(value.clone(), value.clone(), RangeType::Unknown);

                        let true_range =
                            self.apply_comparison(value.clone(), cmp_op, true, const_in_left);
                        let false_range =
                            self.apply_comparison(value.clone(), cmp_op, false, const_in_left);
                        let target_vec = targets.all_targets();
                        let vbm = ValueBranchMap::new(
                            variable,
                            &target_vec[0],
                            &target_vec[1],
                            IntervalType::Basic(BasicInterval::new(true_range)),
                            IntervalType::Basic(BasicInterval::new(false_range)),
                        );
                        self.values_branchmap.insert(&place, vbm);
                    }
                    (None, None) => {
                        let CR = Range::new(T::min_value(), T::max_value(), RangeType::Unknown);

                        let p1 = match op1 {
                            Operand::Copy(p) | Operand::Move(p) => p,
                            _ => panic!("Expected a place"),
                        };
                        let p2 = match op2 {
                            Operand::Copy(p) | Operand::Move(p) => p,
                            _ => panic!("Expected a place"),
                        };
                        let target_vec = targets.all_targets();
                        self.add_varnode(&p1);
                        // print!("add_vbm_varnode{:?}\n", p1.clone());

                        self.add_varnode(&p2);
                        // print!("add_vbm_varnode{:?}\n", p2.clone());

                        let STOp1 = IntervalType::Symb(SymbInterval::new(CR.clone(), p2, true));
                        let SFOp1 = IntervalType::Symb(SymbInterval::new(CR.clone(), p2, false));
                        let STOp2 = IntervalType::Symb(SymbInterval::new(CR.clone(), p1, true));
                        let SFOp2 = IntervalType::Symb(SymbInterval::new(CR.clone(), p1, false));
                        let vbm_1 =
                            ValueBranchMap::new(p1, &target_vec[0], &target_vec[1], STOp1, SFOp1);
                        let vbm_2 =
                            ValueBranchMap::new(p2, &target_vec[0], &target_vec[1], STOp2, SFOp2);
                        self.values_branchmap.insert(&p1, vbm_1);
                        self.values_branchmap.insert(&p2, vbm_2);
                    }
                }
            };
        }
    }

    fn extract_condition(
        &mut self,
        place: &'tcx Place<'tcx>,
        switch_block: &'tcx BasicBlockData<'tcx>,
    ) -> Option<(&'tcx Operand<'tcx>, &'tcx Operand<'tcx>, BinOp)> {
        for stmt in &switch_block.statements {
            if let StatementKind::Assign(box (lhs, Rvalue::BinaryOp(bin_op, box (op1, op2)))) =
                &stmt.kind
            {
                if lhs == place {
                    let mut return_op1: &Operand<'tcx> = &op1;
                    let mut return_op2: &Operand<'tcx> = &op2;
                    for stmt_original in &switch_block.statements {
                        if let StatementKind::Assign(box (lhs, Rvalue::Use(OP1))) =
                            &stmt_original.kind
                        {
                            if lhs.clone() == op1.place().unwrap() {
                                return_op1 = OP1;
                            }
                        }
                    }
                    if op2.constant().is_none() {
                        for stmt_original in &switch_block.statements {
                            if let StatementKind::Assign(box (lhs, Rvalue::Use(OP2))) =
                                &stmt_original.kind
                            {
                                if lhs.clone() == op2.place().unwrap() {
                                    return_op2 = OP2;
                                }
                            }
                        }
                    }
                    return Some((return_op1, return_op2, *bin_op));
                }
            }
        }
        None
    }

    fn apply_comparison<U: IntervalArithmetic>(
        &self,
        constant: U,
        cmp_op: BinOp,
        is_true_branch: bool,
        const_in_left: bool,
    ) -> Range<U> {
        match cmp_op {
            BinOp::Lt => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Le => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Gt => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Ge => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Eq => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            _ => Range::new(constant.clone(), constant.clone(), RangeType::Empty),
        }
    }

    fn build_value_goto_map(&self, block_index: BasicBlock, target: BasicBlock) {
        // print!(
        //     "Building value map for Goto in block {:?} targeting block {:?}",
        //     block_index, target
        // );
    }
    pub fn build_varnodes(&mut self) {
        // Builds VarNodes
        for (name, node) in self.vars.iter_mut() {
            let is_undefined = !self.defmap.contains_key(name);
            node.init(is_undefined);
        }
    }
    pub fn build_symbolic_intersect_map(&mut self) {
        for i in 0..self.oprs.len() {
            if let BasicOpKind::Essa(essaop) = &self.oprs[i] {
                if let IntervalType::Symb(symbi) = essaop.get_intersect() {
                    let v = symbi.get_bound();
                    self.symbmap.entry(v).or_insert_with(HashSet::new).insert(i);
                    // print!("sym_map insert {:?} {:?}\n", v, essaop);
                }
            }
        }
    }
    pub fn build_use_map(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
    ) -> HashMap<&'tcx Place<'tcx>, HashSet<usize>> {
        // Builds use map
        let mut comp_use_map = HashMap::new();
        for &place in component {
            if let Some(uses) = self.usemap.get(place) {
                for op in uses.iter() {
                    let sink = self.oprs[*op].get_sink();
                    if component.contains(&sink) {
                        comp_use_map
                            .entry(sink)
                            .or_insert_with(HashSet::new)
                            .insert(*op);
                    }
                }
            }
        }

        // self.print_compusemap(component, &comp_use_map);
        comp_use_map
    }
    pub fn build_operations(&mut self, inst: &'tcx Statement<'tcx>, block: BasicBlock) {
        if let StatementKind::Assign(box (sink, rvalue)) = &inst.kind {
            match rvalue {
                Rvalue::BinaryOp(op, box (op1, op2)) => match op {
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::AddUnchecked => {
                        self.add_binary_op(sink, inst, op1, op2);
                    }
                    BinOp::AddWithOverflow => {
                        self.add_binary_op(sink, inst, op1, op2);
                    }
                    BinOp::SubUnchecked => {
                        self.add_binary_op(sink, inst, op1, op2);
                    }
                    BinOp::SubWithOverflow => {
                        self.add_binary_op(sink, inst, op1, op2);
                    }
                    BinOp::MulUnchecked => {
                        self.add_binary_op(sink, inst, op1, op2);
                    }
                    BinOp::MulWithOverflow => {
                        self.add_binary_op(sink, inst, op1, op2);
                    }

                    _ => {}
                },
                Rvalue::UnaryOp(UnOp, op) => {
                    self.add_unary_op(sink, inst, op);
                }
                Rvalue::Aggregate(kind, operends) => {
                    match **kind {
                        AggregateKind::Adt(def_id, _, _, _, _) => {
                            if def_id == self.essa {
                                self.add_essa_op(sink, inst, operends, block);
                                // print!("Adt{:?}\n", operends);
                            }
                            if def_id == self.ssa {
                                self.add_ssa_op(sink, inst, operends);
                                // print!("Adt{:?}\n", operends);
                            }
                        }
                        _ => {}
                    }
                }
                Rvalue::Use(operend) => {
                    self.add_use_op(sink, inst, operend);
                }
                _ => {}
            }
        }
    }
    fn add_ssa_op(
        &mut self,
        sink: &'tcx Place<'tcx>,

        inst: &'tcx Statement<'tcx>,
        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
    ) {
        // print!("ssa_op{:?}\n", inst);

        let sink_node = self.add_varnode(sink);
        // print!("addsink_in_ssa_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let mut phiop = PhiOp::new(IntervalType::Basic(BI), sink, inst, 0);
        let bop_index = self.oprs.len();
        for i in 0..operands.len() {
            let source = match &operands[FieldIdx::from_usize(i)] {
                Operand::Copy(place) | Operand::Move(place) => Some(place),
                _ => None,
            };
            if let Some(source) = source {
                self.add_varnode(source);
                phiop.add_source(source);
                // print!("addvar_in_ssa_op{:?}\n", source);
                self.usemap.entry(source).or_default().insert(bop_index);
            }
        }
        // Insert the operation in the graph.

        self.oprs.push(BasicOpKind::Phi(phiop));

        // Insert this definition in defmap

        self.defmap.insert(sink, bop_index);
    }
    fn add_use_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        op: &'tcx Operand<'tcx>,
    ) {
        // print!("use_op{:?}\n", inst);

        let sink_node = self.add_varnode(sink);
        // print!("addsink_in_use_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let mut source: Option<&'tcx Place<'tcx>> = None;

        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                source = Some(place);
                if let Some(source) = source {
                    // print!("addvar_in_use_op{:?}\n", source);

                    let useop = UseOp::new(IntervalType::Basic(BI), sink, inst, source, 0);
                    // Insert the operation in the graph.
                    let bop_index = self.oprs.len();

                    self.oprs.push(BasicOpKind::Use(useop));
                    // Insert this definition in defmap
                    self.usemap.entry(source).or_default().insert(bop_index);

                    self.defmap.insert(sink, bop_index);
                }
            }
            Operand::Constant(constant) => {
                // print!("add_constant_op{:?}\n", inst);
                let Some(c) = op.constant() else {
                    return;
                };
                if let Some(value) = Self::convert_const(&c.const_) {
                    sink_node.set_range(Range::new(
                        value.clone(),
                        value.clone(),
                        RangeType::Regular,
                    ));
                } else {
                }
            }
        }
    }
    fn add_essa_op(
        &mut self,
        sink: &'tcx Place<'tcx>,

        inst: &'tcx Statement<'tcx>,
        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
        block: BasicBlock,
    ) {
        // print!("essa_op{:?}\n", inst);
        let sink_node = self.add_varnode(sink);
        // print!("addsink_in_essa_op{:?}\n", sink_node);

        // let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let loc_1: usize = 0;
        let loc_2: usize = 1;
        let source1 = match &operands[FieldIdx::from_usize(loc_1)] {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            _ => None,
        };
        // print!("addvar_in_essa_op{:?}\n", source1.unwrap());
        let op = &operands[FieldIdx::from_usize(loc_2)];
        let bop_index = self.oprs.len();

        let BI: IntervalType<'_, T>;
        if let Operand::Constant(c) = op {
            BI = IntervalType::Basic(BasicInterval::new(Range::default(T::min_value())));
            self.usemap
                .entry(source1.unwrap())
                .or_default()
                .insert(bop_index);
            // print!("addvar_in_essa_op{:?}in \n", source1.unwrap());
        } else {
            let vbm = self.values_branchmap.get(source1.unwrap()).unwrap();
            if block == *vbm.get_bb_true() {
                // print!("essa_op true branch{:?}\n", block);
                BI = vbm.get_itv_t();
            } else {
                // println!("essa_op false branch{:?}\n", block);
                BI = vbm.get_itv_f();
            }
            let source2 = match op {
                Operand::Copy(place) | Operand::Move(place) => Some(place),
                _ => None,
            };
            self.usemap
                .entry(source2.unwrap())
                .or_default()
                .insert(bop_index);
            // println!("addvar_in_essa_op{:?}in \n", source2.unwrap());
        }

        let essaop = EssaOp::new(BI, sink, inst, source1.unwrap(), 0);
        // Insert the operation in the graph.

        self.oprs.push(BasicOpKind::Essa(essaop));
        // Insert this definition in defmap
        // self.usemap
        //     .entry(source1.unwrap())
        //     .or_default()
        //     .insert(bop_index);

        self.defmap.insert(sink, bop_index);
    }
    fn add_unary_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        op: &'tcx Operand<'tcx>,
    ) {
        // print!("unary_op{:?}\n", inst);

        let sink_node = self.add_varnode(sink);
        // println!("addsink_in_unary_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));
        let loc_1: usize = 0;
        let source = match op {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            _ => None,
        };
        // println!("addvar_in_unary_op{:?}\n", source.unwrap());
        self.add_varnode(source.unwrap());

        let unaryop = UnaryOp::new(IntervalType::Basic(BI), sink, inst, source.unwrap(), 0);
        // Insert the operation in the graph.
        let bop_index = self.oprs.len();

        self.oprs.push(BasicOpKind::Unary(unaryop));
        // Insert this definition in defmap

        self.defmap.insert(sink, bop_index);
    }

    fn add_binary_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        op1: &'tcx Operand<'tcx>,
        op2: &'tcx Operand<'tcx>,
    ) {
        // print!("binary_op{:?}\n", inst);
        let sink_node = self.add_varnode(sink);
        // println!("addsink_in_binary_op{:?}\n", sink_node);
        let bop_index = self.oprs.len();
        let BI: BasicInterval<T> = BasicInterval::new(Range::default(T::min_value()));

        let source1_place = match op1 {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                // println!("addvar_in_binary_op{:?}\n", place);

                Some(place)
            }
            Operand::Constant(_) => None,
        };

        match op2 {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                // println!("addvar_in_binary_op{:?}\n", place);

                let source2_place = Some(place);
                let BOP = BinaryOp::new(
                    IntervalType::Basic(BI),
                    sink,
                    inst,
                    source1_place,
                    source2_place,
                    0,
                    None,
                );
                self.oprs.push(BasicOpKind::Binary(BOP));
                // let bop_ref = unsafe { &*(self.oprs.last().unwrap() as *const BasicOp<'tcx, T>) };
                self.defmap.insert(sink, bop_index);
                if let Some(place) = source1_place {
                    self.usemap.entry(place).or_default().insert(bop_index);
                }

                if let Some(place) = source2_place {
                    self.usemap.entry(place).or_default().insert(bop_index);
                }
            }
            Operand::Constant(c) => {
                let const_value = Self::convert_const(&c.const_).unwrap();
                let BOP = BinaryOp::new(
                    IntervalType::Basic(BI),
                    sink,
                    inst,
                    source1_place,
                    None,
                    0,
                    Some(const_value),
                );
                self.oprs.push(BasicOpKind::Binary(BOP));
                // let bop_ref = unsafe { &*(self.oprs.last().unwrap() as *const BasicOp<'tcx, T>) };
                self.defmap.insert(sink, bop_index);
                if let Some(place) = source1_place {
                    self.usemap.entry(place).or_default().insert(bop_index);
                }
            }
        };

        // print!("varnodes{:?}\n", self.vars);
        // print!("defmap{:?}\n", self.defmap);
        // print!("usemap{:?}\n", self.usemap);
        // print!("{:?}add_binary_op{:?}\n", inst,sink);
        // ...
    }
    fn fix_intersects(&mut self, component: &HashSet<&'tcx Place<'tcx>>) {
        // 处理交集
        for &place in component.iter() {
            let node = self.vars.get(place).unwrap();
            // node.fix_intersects();

            if let Some(sit) = self.symbmap.get_mut(place) {
                for &op in sit.iter() {
                    let op = &mut self.oprs[op];
                    op.op_fix_intersects(node);
                }
            }
        }
    }
    pub fn widen(&mut self, op: usize) -> bool {
        // use crate::range_util::{get_first_less_from_vector, get_first_greater_from_vector};

        // assert!(!constant_vector.is_empty(), "Invalid constant vector");
        let op = &mut self.oprs[op];
        let old_interval = op.get_intersect().get_range().clone();
        let new_interval = op.eval(&self.vars);

        let old_lower = old_interval.get_lower();
        let old_upper = old_interval.get_upper();
        let new_lower = new_interval.get_lower();
        let new_upper = new_interval.get_upper();

        // let nlconstant = get_first_less_from_vector(constant_vector, new_lower);
        // let nuconstant = get_first_greater_from_vector(constant_vector, new_upper);
        // let nlconstant = constant_vector
        //     .iter()
        //     .find(|&&c| c <= new_lower)
        //     .cloned()
        //     .unwrap_or(T::min_value());
        // let nuconstant = constant_vector
        //     .iter()
        //     .find(|&&c| c >= new_upper)
        //     .cloned()
        //     .unwrap_or(T::max_value());
        let nlconstant = new_lower.clone();
        let nuconstant = new_upper.clone();
        let updated = if old_interval.is_unknown() {
            new_interval
        } else if new_lower < old_lower && new_upper > old_upper {
            Range::new(nlconstant, nuconstant, RangeType::Regular)
        } else if new_lower < old_lower {
            Range::new(nlconstant, old_upper.clone(), RangeType::Regular)
        } else if new_upper > old_upper {
            Range::new(old_lower.clone(), nuconstant, RangeType::Regular)
        } else {
            old_interval.clone()
        };

        op.set_intersect(updated.clone());

        let sink = op.get_sink();
        let new_sink_interval = op.get_intersect().get_range().clone();
        self.vars
            .get_mut(sink)
            .unwrap()
            .set_range(new_sink_interval.clone());
        // println!(
        //     "WIDEN::{:?}: {:?} -> {:?}",
        //     sink, old_interval, new_sink_interval
        // );

        old_interval != new_sink_interval
    }
    pub fn narrow(&mut self, op: &mut BasicOpKind<'tcx, T>) -> bool {
        let old_range = self.vars[op.get_sink()].get_range();
        let o_lower = old_range.get_lower().clone();
        let o_upper = old_range.get_upper().clone();

        let new_range = op.eval(&self.vars);
        let n_lower = new_range.get_lower().clone();
        let n_upper = new_range.get_upper().clone();

        let mut has_changed = false;
        let min = T::min_value();
        let max = T::max_value();

        let mut result_lower = o_lower.clone();
        let mut result_upper = o_upper.clone();

        if o_lower == min && n_lower != min {
            result_lower = n_lower;
            has_changed = true;
        } else {
            // let smin = o_lower.clone().min(n_lower.clone());
            let smin = T::min_value();
            if o_lower != smin {
                result_lower = smin;
                has_changed = true;
            }
        }

        if o_upper == max && n_upper != max {
            result_upper = n_upper;
            has_changed = true;
        } else {
            // let smax = o_upper.clone().max(n_upper.clone());
            let smax = T::max_value();
            if o_upper != smax {
                result_upper = smax;
                has_changed = true;
            }
        }

        if has_changed {
            let new_sink_range = Range::new(
                result_lower.clone(),
                result_upper.clone(),
                RangeType::Regular,
            );
            let sink_node = self.vars.get_mut(op.get_sink()).unwrap();
            sink_node.set_range(new_sink_range.clone());

            // println!(
            //     "NARROW::{}: {:?} -> {:?}",
            // ,
            //     Range::new(o_lower, o_upper),
            //     new_sink_range
            // );
        }

        has_changed
    }
    fn pre_update(
        &mut self,
        comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        entry_points: &HashSet<&'tcx Place<'tcx>>,
    ) {
        let mut worklist: Vec<&'tcx Place<'tcx>> = entry_points.iter().cloned().collect();
        let mut visited: HashSet<&'tcx Place<'tcx>> = entry_points.clone();

        while let Some(place) = worklist.pop() {
            if let Some(op_set) = comp_use_map.get(place) {
                for &op in op_set {
                    if self.widen(op) {
                        let sink = self.oprs[op].get_sink();
                        // let sink_node = self.vars.get_mut(sink).unwrap();
                        if visited.insert(sink) {
                            worklist.push(sink);
                        }
                    }
                }
            }
        }
    }

    fn pos_update(
        &mut self,
        _comp_use_map: &HashMap<&'tcx Place<'tcx>, HashSet<usize>>,
        _entry_points: &HashSet<&'tcx Place<'tcx>>,
        _component: &HashSet<&'tcx Place<'tcx>>,
    ) {
        // TODO: Implement the logic for pre_update as needed.
    }
    fn generate_active_vars(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        active_vars: &mut HashSet<&'tcx Place<'tcx>>,
    ) {
        for place in component {
            let node = self.vars.get(place).unwrap();
        }
    }
    fn generate_entry_points(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
        entry_points: &mut HashSet<&'tcx Place<'tcx>>,
    ) {
        for &place in component {
            let op = self.defmap.get(place).unwrap();
            // if let BasicOpKind::Essa(essaop) = &mut self.oprs[*op] {
            //     if essaop.is_unresolved() {
            //         let source = essaop.get_source();
            //         let new_range = essaop.eval(&self.vars);
            //         let sink_node = self.vars.get_mut(source).unwrap();
            //         sink_node.set_range(new_range);
            //     }
            //     essaop.mark_resolved();
            // }
            if !self.vars[place].get_range().is_unknown() {
                entry_points.insert(place);
            }
        }
    }
    fn propagate_to_next_scc(&mut self, component: &HashSet<&'tcx Place<'tcx>>) {
        for &place in component.iter() {
            let node = self.vars.get_mut(place).unwrap();
            for &op in self.usemap.get(place).unwrap().iter() {
                let op = &mut self.oprs[op];
                let sink = op.get_sink();
                let new_range = op.eval(&self.vars);
                let sink_node = self.vars.get_mut(sink).unwrap();
                // println!(
                //     "component {:?} set {:?} to {:?} through{:?}\n",
                //     component,
                //     new_range,
                //     sink,
                //     op.get_instruction()
                // );
                sink_node.set_range(new_range);

                if let BasicOpKind::Essa(essaop) = op {
                    if essaop.get_intersect().get_range().is_unknown() {
                        essaop.mark_unresolved();
                    }
                }
            }
        }
    }
    pub fn find_intervals(&mut self) {
        // 构建符号交集映射
        self.build_symbolic_intersect_map();

        // let scc_list = Nuutila::new(&self.vars, &self.usemap, &self.symbmap,false,&self.oprs);
        // self.print_vars();
        self.numSCCs = self.worklist.len();
        let components: Vec<HashSet<&'tcx Place<'tcx>>> =
            self.components.values().cloned().collect();
        for component in components {
            // print!("===start component {:?}===\n", component);
            if component.len() == 1 {
                self.numAloneSCCs += 1;

                self.fix_intersects(&component);

                let variable: &Place<'tcx> = *component.iter().next().unwrap();
                let varnode = self.vars.get_mut(variable).unwrap();
                if varnode.get_range().is_unknown() {
                    varnode.set_default();
                }
            } else {
                // self.pre_update(&comp_use_map, &entry_points);
                let comp_use_map = self.build_use_map(&component);
                // build_constant_vec(&component, &self.oprs, &mut self.constant_vec);
                let mut entry_points = HashSet::new();
                // self.print_vars();

                self.generate_entry_points(&component, &mut entry_points);
                // print!(
                //     "component {:?} entry_points{:?}  \n ",
                //     component, entry_points
                // );
                self.pre_update(&comp_use_map, &entry_points);
                // self.fix_intersects(&component);

                for &variable in &component {
                    let varnode = self.vars.get_mut(variable).unwrap();
                    if varnode.get_range().is_unknown() {
                        varnode.set_default();
                    }
                }

                let mut active_vars = HashSet::new();
                self.generate_active_vars(&component, &mut active_vars);
                self.pos_update(&comp_use_map, &active_vars, &component);
            }
            self.propagate_to_next_scc(&component);
        }
    }

    pub fn build_nuutila(&mut self, single: bool) {
        // print!("====Building graph====\n");

        if single {
        } else {
            for place in self.vars.keys().copied() {
                self.dfs.insert(place, -1);
            }

            // n.add_control_dependence_edges(, use_map, varNodes);

            let places: Vec<_> = self.vars.keys().copied().collect();

            for place in places {
                if self.dfs[&place] < 0 {
                    let mut stack = Vec::new();
                    self.visit(place, &mut stack);
                    // print!("place{:?}\n", place);
                }
            }

            // n.del_control_dependence_edges(use_map);
        }
        // print!("components{:?}\n", self.components);
        // print!("worklist{:?}\n", self.worklist);
        // print!("dfs{:?}\n", self.dfs);
    }
    pub fn visit(&mut self, place: &'tcx Place<'tcx>, stack: &mut Vec<&'tcx Place<'tcx>>) {
        self.dfs.entry(place).and_modify(|v| *v = self.index);
        self.index += 1;
        self.root.insert(place, place);
        let uses = self.usemap.get(place).unwrap().clone();
        for op in uses {
            let name = self.oprs[op].get_sink();
            // print!("place {:?} get name{:?}\n", place, name);
            if self.dfs.get(name).copied().unwrap_or(-1) < 0 {
                self.visit(name, stack);
            }

            if !self.in_component.contains(name)
                && self.dfs[self.root[place]] >= self.dfs[self.root[name]]
            {
                *self.root.get_mut(place).unwrap() = self.root.get(name).copied().unwrap();

                // let weq = self.root.get(place)
            }
        }

        if self.root.get(place).copied().unwrap() == place {
            self.worklist.push_back(place);

            let mut scc = HashSet::new();
            scc.insert(place);

            self.in_component.insert(place);

            while let Some(top) = stack.last() {
                if self.dfs.get(top).copied().unwrap_or(-1) > self.dfs.get(place).copied().unwrap()
                {
                    let node = stack.pop().unwrap();
                    self.in_component.insert(node);

                    scc.insert(node);
                } else {
                    break;
                }
            }

            self.components.insert(place, scc);
        } else {
            stack.push(place);
        }
    }
}
#[derive(Debug)]
pub struct Nuutila<'tcx, T: IntervalArithmetic + Debug> {
    pub variables: &'tcx VarNodes<'tcx, T>,
    pub index: i32,
    pub dfs: HashMap<&'tcx Place<'tcx>, i32>,
    pub root: HashMap<&'tcx Place<'tcx>, &'tcx Place<'tcx>>,
    pub in_component: HashSet<&'tcx Place<'tcx>>,
    pub components: HashMap<&'tcx Place<'tcx>, HashSet<&'tcx Place<'tcx>>>,
    pub worklist: VecDeque<&'tcx Place<'tcx>>,
    // pub oprs: &Vec<BasicOpKind<'tcx, T>>,
}

impl<'tcx, T> Nuutila<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    pub fn new(
        varNodes: &'tcx VarNodes<'tcx, T>,
        use_map: &'tcx UseMap<'tcx>,
        symb_map: &'tcx SymbMap<'tcx>,
        single: bool,
        oprs: &'tcx Vec<BasicOpKind<'tcx, T>>,
    ) -> Self {
        let mut n = Nuutila {
            variables: varNodes,
            index: 0,
            dfs: HashMap::new(),
            root: HashMap::new(),
            in_component: HashSet::new(),
            components: HashMap::new(),
            worklist: std::collections::VecDeque::new(),
            // oprs:oprs
        };

        if single {
            // let mut scc = HashSet::new();
            // for var_node in variables.values() {
            //     scc.insert(var_node.clone());
            // }

            // for (place, _) in variables.iter() {
            //     n.components.insert(place.clone(), scc.clone());
            // }

            // if let Some((first_place, _)) = variables.iter().next() {
            //     n.worklist.push_back(first_place.clone());
            // }
        } else {
            for place in n.variables.keys().copied() {
                n.dfs.insert(place, -1);
            }

            n.add_control_dependence_edges(symb_map, use_map, varNodes);

            for place in n.variables.keys() {
                if n.dfs[place] < 0 {
                    let mut stack = Vec::new();
                    n.visit(place, &mut stack, use_map, oprs);
                }
            }

            // n.del_control_dependence_edges(use_map);
        }

        n
    }

    pub fn visit(
        &mut self,
        place: &'tcx Place<'tcx>,
        stack: &mut Vec<&'tcx Place<'tcx>>,
        use_map: &'tcx UseMap<'tcx>,
        oprs: &'tcx Vec<BasicOpKind<'tcx, T>>,
    ) {
        self.dfs.entry(place).and_modify(|v| *v = self.index);
        self.index += 1;
        self.root.insert(place, place);

        if let Some(uses) = use_map.get(place) {
            for op in uses {
                let name = oprs[*op].get_sink();

                if self.dfs.get(name).copied().unwrap_or(-1) < 0 {
                    self.visit(name, stack, use_map, oprs);
                }

                if !self.in_component.contains(name)
                    && self.dfs[self.root[place]] >= self.dfs[self.root[name]]
                {
                    *self.root.get_mut(place).unwrap() = self.root.get(name).copied().unwrap();

                    // let weq = self.root.get(place)
                }
            }
        }

        if self.root.get(place).copied().unwrap() == place {
            self.worklist.push_back(place);

            let mut scc = HashSet::new();
            scc.insert(place);

            self.in_component.insert(place);

            while let Some(&top) = stack.last() {
                if self.dfs.get(top).copied().unwrap_or(-1) > self.dfs.get(place).copied().unwrap()
                {
                    let node = stack.pop().unwrap();
                    self.in_component.insert(node);

                    scc.insert(node);
                } else {
                    break;
                }
            }

            self.components.insert(place, scc);
        } else {
            stack.push(place);
        }
    }

    pub fn add_control_dependence_edges(
        &mut self,
        _symb_map: &'tcx SymbMap<'tcx>,
        _use_map: &'tcx UseMap<'tcx>,
        _vars: &'tcx VarNodes<'tcx, T>,
    ) {
        todo!()
    }

    pub fn del_control_dependence_edges(&mut self, _use_map: &'tcx mut UseMap<'tcx>) {
        todo!()
    }
}
