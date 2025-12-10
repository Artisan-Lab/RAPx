use crate::{
    analysis::{
        Analysis,
        core::{
            alias_analysis::AAResult,
            ownedheap_analysis::OHAResultMap,
            range_analysis::{RangeAnalysis, default::RangeAnalyzer},
        },
        safedrop::graph::SafeDropGraph,
        senryx::{
            contracts::property::{CisRangeItem, PropertyContract},
            symbolic_analysis::{AnaOperand, SymbolicDef, ValueDomain},
        },
        utils::{draw_dot::render_dot_string, fn_info::*, show_mir::display_mir},
    },
    rap_debug, rap_warn,
};
use rustc_middle::ty::GenericParamDefKind;
use serde::de;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};
use syn::Constraint;

use super::contracts::abstract_state::{
    AbstractStateItem, AlignState, PathInfo, StateType, VType, Value,
};
use super::dominated_graph::DominatedGraph;
use super::dominated_graph::InterResultNode;
use super::generic_check::GenericChecker;
use super::inter_record::InterAnalysisRecord;
use super::matcher::UnsafeApi;
use super::matcher::{get_arg_place, parse_unsafe_api};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        self, AggregateKind, BasicBlock, BasicBlockData, BinOp, CastKind, Local, Operand, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{self, GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};
use rustc_span::{Span, source_map::Spanned};

//TODO: modify contracts vec to contract-bool pairs (we can also use path index to record path info)
pub struct CheckResult {
    pub func_name: String,
    pub func_span: Span,
    pub failed_contracts: HashMap<usize, HashSet<String>>,
    pub passed_contracts: HashMap<usize, HashSet<String>>,
}

impl CheckResult {
    pub fn new(func_name: &str, func_span: Span) -> Self {
        Self {
            func_name: func_name.to_string(),
            func_span,
            failed_contracts: HashMap::new(),
            passed_contracts: HashMap::new(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PlaceTy<'tcx> {
    Ty(usize, usize), // layout(align,size) of one specific type
    GenericTy(String, HashSet<Ty<'tcx>>, HashSet<(usize, usize)>), // get specific type in generic map
    Unknown,
}

impl<'tcx> PlaceTy<'tcx> {
    pub fn possible_aligns(&self) -> HashSet<usize> {
        match self {
            PlaceTy::Ty(align, _size) => {
                let mut set = HashSet::new();
                set.insert(*align);
                set
            }
            PlaceTy::GenericTy(_, _, tys) => tys.iter().map(|ty| ty.0).collect(),
            _ => HashSet::new(),
        }
    }
}

impl<'tcx> Hash for PlaceTy<'tcx> {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

pub struct BodyVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub safedrop_graph: SafeDropGraph<'tcx>,
    // abstract_states records the path index and variables' ab states in this path
    pub abstract_states: HashMap<usize, PathInfo<'tcx>>,
    pub unsafe_callee_report: HashMap<String, usize>,
    pub local_ty: HashMap<usize, PlaceTy<'tcx>>,
    pub visit_time: usize,
    pub check_results: Vec<CheckResult>,
    pub generic_map: HashMap<String, HashSet<Ty<'tcx>>>,
    pub global_recorder: HashMap<DefId, InterAnalysisRecord<'tcx>>,
    pub proj_ty: HashMap<usize, Ty<'tcx>>,
    pub chains: DominatedGraph<'tcx>,
    pub value_domains: HashMap<usize, ValueDomain>,
    pub path_constraints: Vec<SymbolicDef>,
}

impl<'tcx> BodyVisitor<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        global_recorder: HashMap<DefId, InterAnalysisRecord<'tcx>>,
        visit_time: usize,
    ) -> Self {
        let body = tcx.optimized_mir(def_id);
        let param_env = tcx.param_env(def_id);
        let satisfied_ty_map_for_generic =
            GenericChecker::new(tcx, param_env).get_satisfied_ty_map();
        let mut chains = DominatedGraph::new(tcx, def_id);
        chains.init_arg();
        Self {
            tcx,
            def_id,
            safedrop_graph: SafeDropGraph::new(body, tcx, def_id, OHAResultMap::default()),
            abstract_states: HashMap::new(),
            unsafe_callee_report: HashMap::new(),
            local_ty: HashMap::new(),
            visit_time,
            check_results: Vec::new(),
            generic_map: satisfied_ty_map_for_generic,
            global_recorder,
            proj_ty: HashMap::new(),
            chains,
            value_domains: HashMap::new(),
            path_constraints: Vec::new(),
            // paths: HashSet::new(),
        }
    }

    pub fn get_ty_by_place(&self, p: usize) -> Ty<'tcx> {
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        return locals[Local::from(p)].ty;
    }

    pub fn update_fields_states(&mut self, inter_result: InterResultNode<'tcx>) {
        self.chains.init_self_with_inter(inter_result);
    }

    pub fn path_forward_check(
        &mut self,
        fn_map: &FxHashMap<DefId, AAResult>,
    ) -> InterResultNode<'tcx> {
        let mut inter_return_value =
            InterResultNode::construct_from_var_node(self.chains.clone(), 0);
        if self.visit_time >= 1000 {
            return inter_return_value;
        }
        // get path and body
        let paths = self.get_all_paths();
        let body = self.tcx.optimized_mir(self.def_id);
        let target_name = get_cleaned_def_path_name(self.tcx, self.def_id);
        // initialize local vars' types
        let locals = body.local_decls.clone();
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            let layout = self.visit_ty_and_get_layout(local_ty);
            self.local_ty.insert(idx, layout);
        }

        // Iterate all the paths. Paths have been handled by tarjan.
        let tmp_chain = self.chains.clone();
        for (index, (path, constraint)) in paths.iter().enumerate() {
            self.value_domains.clear();
            self.chains = tmp_chain.clone();
            self.set_constraint(constraint);
            self.abstract_states.insert(index, PathInfo::new());
            for (i, block_index) in path.iter().enumerate() {
                if block_index >= &body.basic_blocks.len() {
                    continue;
                }
                let next_block = path.get(i + 1).cloned();
                self.path_analyze_block(
                    &body.basic_blocks[BasicBlock::from_usize(*block_index)].clone(),
                    index,
                    *block_index,
                    next_block,
                    fn_map,
                );
                let tem_scc_sub_blocks = self.safedrop_graph.blocks[*block_index]
                    .scc_sub_blocks
                    .clone();
                if tem_scc_sub_blocks.len() > 0 {
                    for sub_block in &tem_scc_sub_blocks {
                        self.path_analyze_block(
                            &body.basic_blocks[BasicBlock::from_usize(*sub_block)].clone(),
                            index,
                            *block_index,
                            next_block,
                            fn_map,
                        );
                    }
                }
            }

            // Used for debug
            if self.visit_time == 0 {
                let base_name = get_cleaned_def_path_name(self.tcx, self.def_id);
                let path_suffix = path
                    .iter()
                    .map(|b| b.to_string())
                    .collect::<Vec<String>>()
                    .join("_");

                let name = format!("{}_path_{}", base_name, path_suffix);
                let dot_string = self.chains.to_dot_graph();
                render_dot_string(name, dot_string);
            }

            // merge path analysis results
            let curr_path_inter_return_value =
                InterResultNode::construct_from_var_node(self.chains.clone(), 0);
            inter_return_value.merge(curr_path_inter_return_value);
        }

        inter_return_value
    }

    pub fn path_analyze_block(
        &mut self,
        block: &BasicBlockData<'tcx>,
        path_index: usize,
        bb_index: usize,
        next_block: Option<usize>,
        fn_map: &FxHashMap<DefId, AAResult>,
    ) {
        for statement in block.statements.iter() {
            self.path_analyze_statement(statement, path_index);
        }
        self.path_analyze_terminator(
            &block.terminator(),
            path_index,
            bb_index,
            next_block,
            fn_map,
        );
    }

    pub fn path_analyze_statement(&mut self, statement: &Statement<'tcx>, _path_index: usize) {
        match statement.kind {
            StatementKind::Assign(box (ref lplace, ref rvalue)) => {
                self.path_analyze_assign(lplace, rvalue, _path_index);
            }
            StatementKind::Intrinsic(box ref intrinsic) => match intrinsic {
                mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                    if cno.src.place().is_some() && cno.dst.place().is_some() {
                        let _src_pjc_local =
                            self.handle_proj(true, cno.src.place().unwrap().clone());
                        let _dst_pjc_local =
                            self.handle_proj(true, cno.dst.place().unwrap().clone());
                    }
                }
                _ => {}
            },
            StatementKind::StorageDead(local) => {}
            _ => {}
        }
    }
}

/// Implementation for teminator
impl<'tcx> BodyVisitor<'tcx> {
    pub fn path_analyze_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        path_index: usize,
        bb_index: usize,
        next_block: Option<usize>,
        fn_map: &FxHashMap<DefId, AAResult>,
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination: dst_place,
                target: _,
                unwind: _,
                call_source: _,
                fn_span,
            } => {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(callee_def_id, raw_list) = func_constant.const_.ty().kind() {
                        let mut mapping = FxHashMap::default();
                        self.get_generic_mapping(raw_list.as_slice(), callee_def_id, &mut mapping);
                        rap_debug!(
                            "func {:?}, generic type mapping {:?}",
                            callee_def_id,
                            mapping
                        );
                        self.handle_call(
                            dst_place,
                            callee_def_id,
                            args,
                            path_index,
                            fn_map,
                            *fn_span,
                            mapping,
                        );
                    }
                }
            }
            TerminatorKind::Drop {
                place,
                target: _,
                unwind: _,
                replace: _,
                drop: _,
                async_fut: _,
            } => {
                let drop_local = self.handle_proj(false, *place);
                if !self.chains.set_drop(drop_local) {
                    // rap_warn!(
                    //     "In path {:?}, double drop {drop_local} in block {bb_index}",
                    //     self.paths[path_index]
                    // );
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                if let Some(next_bb) = next_block {
                    self.handle_switch_int(discr, targets, next_bb);
                }
            }
            _ => {}
        }
    }

    /// Get the generic name to an actual type mapping when used for a def_id.
    /// If current def_id doesn't have generic, then search its parent.
    /// The generic set include type and allocator.
    /// Example: generic_mapping (T -> u32, A -> std::alloc::Global)
    fn get_generic_mapping(
        &self,
        raw_list: &[rustc_middle::ty::GenericArg<'tcx>],
        def_id: &DefId,
        generic_mapping: &mut FxHashMap<String, Ty<'tcx>>,
    ) {
        let generics = self.tcx.generics_of(def_id);
        for param in &generics.own_params {
            if let GenericParamDefKind::Type {
                has_default: _,
                synthetic: _,
            } = param.kind
            {
                if let Some(ty) = raw_list.get(param.index as usize) {
                    if let GenericArgKind::Type(actual_ty) = (*ty).kind() {
                        let param_name = param.name.to_string();
                        generic_mapping.insert(param_name, actual_ty);
                    }
                }
            }
        }
        if generics.own_params.len() == 0 && generics.parent.is_some() {
            let parent_def_id = generics.parent.unwrap();
            self.get_generic_mapping(raw_list, &parent_def_id, generic_mapping);
        }
    }
}

/// Implementation for statements
impl<'tcx> BodyVisitor<'tcx> {
    pub fn path_analyze_assign(
        &mut self,
        lplace: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        path_index: usize,
    ) {
        let lpjc_local = self.handle_proj(false, lplace.clone());
        match rvalue {
            Rvalue::Use(op) => {
                if let Some(ana_op) = self.lift_operand(op) {
                    let def = match ana_op {
                        AnaOperand::Local(src) => SymbolicDef::Use(src),
                        AnaOperand::Const(val) => SymbolicDef::Constant(val),
                    };
                    self.record_value_def(lpjc_local, def);
                }
                match op {
                    Operand::Move(rplace) => {
                        let rpjc_local = self.handle_proj(true, rplace.clone());
                        self.chains.merge(lpjc_local, rpjc_local);
                    }
                    Operand::Copy(rplace) => {
                        let rpjc_local = self.handle_proj(true, rplace.clone());
                        self.chains.copy_node(lpjc_local, rpjc_local);
                    }
                    _ => {}
                }
            }
            Rvalue::Repeat(op, _const) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local = self.handle_proj(true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::Ref(_, _, rplace) | Rvalue::RawPtr(_, rplace) => {
                let rpjc_local = self.handle_proj(true, rplace.clone());
                self.record_value_def(lpjc_local, SymbolicDef::Ref(rpjc_local));
                self.chains.point(lpjc_local, rpjc_local);
            }
            Rvalue::Cast(cast_kind, op, ty) => {
                if let Some(AnaOperand::Local(src_idx)) = self.lift_operand(op) {
                    self.record_value_def(
                        lpjc_local,
                        SymbolicDef::Cast(src_idx, format!("{:?}", cast_kind)),
                    );
                }
                match op {
                    Operand::Move(rplace) | Operand::Copy(rplace) => {
                        let rpjc_local = self.handle_proj(true, rplace.clone());
                        let r_point_to = self.chains.get_point_to_id(rpjc_local);
                        if r_point_to == rpjc_local {
                            self.chains.merge(lpjc_local, rpjc_local);
                        } else {
                            self.chains.point(lpjc_local, r_point_to);
                        }
                    }
                    _ => {}
                }
            }
            Rvalue::BinaryOp(bin_op, box (op1, op2)) => {
                if let (Some(ana_op1), Some(ana_op2)) =
                    (self.lift_operand(op1), self.lift_operand(op2))
                {
                    let def = match (ana_op1.clone(), ana_op2) {
                        (AnaOperand::Local(l), rhs) => Some(SymbolicDef::Binary(*bin_op, l, rhs)),
                        (AnaOperand::Const(_), AnaOperand::Local(l)) => match bin_op {
                            BinOp::Add
                            | BinOp::Mul
                            | BinOp::BitAnd
                            | BinOp::BitOr
                            | BinOp::BitXor
                            | BinOp::Eq
                            | BinOp::Ne => Some(SymbolicDef::Binary(*bin_op, l, ana_op1)),
                            _ => None,
                        },
                        _ => None,
                    };

                    if let Some(d) = def {
                        self.record_value_def(lpjc_local, d);
                    } else if let (AnaOperand::Const(c), AnaOperand::Local(l)) = (
                        self.lift_operand(op1).unwrap(),
                        self.lift_operand(op2).unwrap(),
                    ) {
                        if matches!(bin_op, BinOp::Add | BinOp::Mul | BinOp::Eq) {
                            self.record_value_def(
                                lpjc_local,
                                SymbolicDef::Binary(*bin_op, l, AnaOperand::Const(c)),
                            );
                        }
                    }
                }
            }
            Rvalue::UnaryOp(un_op, op) => {
                self.record_value_def(lpjc_local, SymbolicDef::UnOp(*un_op));
            }
            Rvalue::ShallowInitBox(op, _ty) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local = self.handle_proj(true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::Aggregate(box agg_kind, op_vec) => match agg_kind {
                AggregateKind::Array(_ty) => {}
                AggregateKind::Adt(_adt_def_id, _, _, _, _) => {
                    for (idx, op) in op_vec.into_iter().enumerate() {
                        let (is_const, val) = get_arg_place(op);
                        if is_const {
                            self.chains.insert_field_node(
                                lpjc_local,
                                idx,
                                Some(Ty::new_uint(self.tcx, rustc_middle::ty::UintTy::Usize)),
                            );
                        } else {
                            let node = self.chains.get_var_node_mut(lpjc_local).unwrap();
                            node.field.insert(idx, val);
                        }
                    }
                }
                _ => {}
            },
            Rvalue::Discriminant(_place) => {}
            _ => {}
        }
    }

    pub fn handle_call(
        &mut self,
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        args: &Box<[Spanned<Operand>]>,
        path_index: usize,
        fn_map: &FxHashMap<DefId, AAResult>,
        fn_span: Span,
        generic_mapping: FxHashMap<String, Ty<'tcx>>,
    ) {
        if !self.tcx.is_mir_available(def_id) {
            return;
        }

        // Find std unsafe API call, then check the contracts.
        if let Some(fn_result) =
            parse_unsafe_api(get_cleaned_def_path_name(self.tcx, *def_id).as_str())
        {
            self.handle_std_unsafe_call(
                dst_place,
                def_id,
                args,
                path_index,
                fn_map,
                fn_span,
                fn_result,
                generic_mapping,
            );
        }

        self.set_bound(def_id, dst_place, args);

        // merge alias results
        self.handle_ret_alias(dst_place, def_id, fn_map, args);
    }

    fn set_bound(
        &mut self,
        def_id: &DefId,
        dst_place: &Place<'tcx>,
        args: &Box<[Spanned<Operand>]>,
    ) {
        if args.len() == 0 || !get_cleaned_def_path_name(self.tcx, *def_id).contains("slice::len") {
            return;
        }
        let d_local = self.handle_proj(false, dst_place.clone());
        let ptr_local = get_arg_place(&args[0].node).1;
        let mem_local = self.chains.get_point_to_id(ptr_local);
        let mem_var = self.chains.get_var_node_mut(mem_local).unwrap();
        for cis in &mut mem_var.cis.contracts {
            if let PropertyContract::InBound(cis_ty, len) = cis {
                *len = CisRangeItem::new_var(d_local);
            }
        }
    }

    // Use the alias analysis to support quick merge inter analysis results.
    pub fn handle_ret_alias(
        &mut self,
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        fn_map: &FxHashMap<DefId, AAResult>,
        args: &Box<[Spanned<Operand>]>,
    ) {
        let d_local = self.handle_proj(false, dst_place.clone());
        // Find alias relationship in cache.
        // If one of the op is ptr, then alias the pointed node with another.
        if let Some(retalias) = fn_map.get(def_id) {
            for alias_set in retalias.aliases() {
                let (l, r) = (alias_set.lhs_no, alias_set.rhs_no);
                let (l_fields, r_fields) =
                    (alias_set.lhs_fields.clone(), alias_set.rhs_fields.clone());
                let (l_place, r_place) = (
                    if l != 0 {
                        get_arg_place(&args[l - 1].node)
                    } else {
                        (false, d_local)
                    },
                    if r != 0 {
                        get_arg_place(&args[r - 1].node)
                    } else {
                        (false, d_local)
                    },
                );
                // if left value is a constant, then update right variable's value
                if l_place.0 {
                    let snd_var = self.chains.find_var_id_with_fields_seq(r_place.1, r_fields);
                    self.chains
                        .update_value(self.chains.get_point_to_id(snd_var), l_place.1);
                    continue;
                }
                // if right value is a constant, then update left variable's value
                if r_place.0 {
                    let fst_var = self.chains.find_var_id_with_fields_seq(l_place.1, l_fields);
                    self.chains
                        .update_value(self.chains.get_point_to_id(fst_var), r_place.1);
                    continue;
                }
                let (fst_var, snd_var) = (
                    self.chains.find_var_id_with_fields_seq(l_place.1, l_fields),
                    self.chains.find_var_id_with_fields_seq(r_place.1, r_fields),
                );
                // If this var is ptr or ref, then get the next level node.
                let fst_to = self.chains.get_point_to_id(fst_var);
                let snd_to = self.chains.get_point_to_id(snd_var);
                let is_fst_point = fst_to != fst_var;
                let is_snd_point = snd_to != snd_var;
                let fst_node = self.chains.get_var_node(fst_var).unwrap();
                let snd_node = self.chains.get_var_node(snd_var).unwrap();
                let is_fst_ptr = is_ptr(fst_node.ty.unwrap()) || is_ref(fst_node.ty.unwrap());
                let is_snd_ptr = is_ptr(snd_node.ty.unwrap()) || is_ref(snd_node.ty.unwrap());
                rap_debug!(
                    "{:?}: {fst_var},{fst_to},{is_fst_ptr} -- {snd_var},{snd_to},{is_snd_ptr}",
                    def_id
                );
                match (is_fst_ptr, is_snd_ptr) {
                    (false, true) => {
                        // If this ptr didn't point to anywhere, then point to fst var
                        if is_snd_point {
                            self.chains.point(snd_var, fst_var);
                        } else {
                            self.chains.merge(fst_var, snd_to);
                        }
                    }
                    (false, false) => {
                        self.chains.merge(fst_var, snd_var);
                    }
                    (true, true) => {
                        if is_fst_point && is_snd_point {
                            self.chains.merge(fst_to, snd_to);
                        } else if !is_fst_point && is_snd_point {
                            self.chains.point(fst_var, snd_to);
                        } else if is_fst_point && !is_snd_point {
                            self.chains.point(snd_var, fst_to);
                        } else {
                            self.chains.merge(fst_var, snd_var);
                        }
                    }
                    (true, false) => {
                        if is_fst_point {
                            self.chains.point(fst_var, snd_var);
                        } else {
                            self.chains.merge(snd_var, fst_to);
                        }
                    }
                }
            }
        }
        // If no alias cache is found and dst is a ptr, then initialize dst's states.
        else {
            let d_ty = self.chains.get_local_ty_by_place(d_local);
            if d_ty.is_some() && (is_ptr(d_ty.unwrap()) || is_ref(d_ty.unwrap())) {
                self.chains
                    .generate_ptr_with_obj_node(d_ty.unwrap(), d_local);
            }
        }
    }

    pub fn get_args_post_states(&mut self) -> HashMap<usize, AbstractStateItem<'tcx>> {
        let tcx = self.tcx;
        let def_id = self.def_id;
        let final_states = self.abstract_states_mop();
        let mut result_states = HashMap::new();
        let fn_sig = tcx.fn_sig(def_id).skip_binder();
        let num_params = fn_sig.inputs().skip_binder().len();
        for i in 0..num_params + 1 {
            if let Some(state) = final_states.state_map.get(&(i)) {
                result_states.insert(i, state.clone());
            } else {
                result_states.insert(i, AbstractStateItem::new_default());
            }
        }
        result_states
    }

    pub fn get_all_paths(&mut self) -> HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> {
        let mut range_analyzer = RangeAnalyzer::<i64>::new(self.tcx, false);
        let path_constraints_option =
            range_analyzer.start_path_constraints_analysis_for_defid(self.def_id); // if def_id does not exist, this will break down
        let mut path_constraints: HashMap<Vec<usize>, Vec<(_, _, _)>> =
            if path_constraints_option.is_none() {
                let mut results = HashMap::new();
                let paths: Vec<Vec<usize>> = self.safedrop_graph.get_paths();
                for path in paths {
                    results.insert(path, Vec::new());
                }
                results
            } else {
                path_constraints_option.unwrap()
            };
        self.safedrop_graph.solve_scc();
        // If it's the first level analysis, then filter the paths not containing unsafe
        if self.visit_time == 0 {
            let contains_unsafe_blocks = get_all_std_unsafe_callees_block_id(self.tcx, self.def_id);
            path_constraints.retain(|path, cons| {
                path.iter()
                    .any(|block_id| contains_unsafe_blocks.contains(block_id))
            });
        }
        // display_hashmap(&path_constraints, 1);
        path_constraints
    }

    pub fn abstract_states_mop(&mut self) -> PathInfo<'tcx> {
        let mut result_state = PathInfo {
            state_map: HashMap::new(),
        };

        for (_path_idx, abstract_state) in &self.abstract_states {
            for (var_index, state_item) in &abstract_state.state_map {
                if let Some(existing_state_item) = result_state.state_map.get_mut(&var_index) {
                    existing_state_item
                        .clone()
                        .meet_state_item(&state_item.clone());
                } else {
                    result_state
                        .state_map
                        .insert(*var_index, state_item.clone());
                }
            }
        }
        result_state
    }

    pub fn update_callee_report_level(&mut self, unsafe_callee: String, report_level: usize) {
        self.unsafe_callee_report
            .entry(unsafe_callee)
            .and_modify(|e| {
                if report_level < *e {
                    *e = report_level;
                }
            })
            .or_insert(report_level);
    }

    // level: 0 bug_level, 1-3 unsound_level
    // TODO: add more information about the result
    pub fn output_results(&self, threshold: usize) {
        for (unsafe_callee, report_level) in &self.unsafe_callee_report {
            if *report_level == 0 {
                rap_warn!("Find one bug in {:?}!", unsafe_callee);
            } else if *report_level <= threshold {
                rap_warn!("Find an unsoundness issue in {:?}!", unsafe_callee);
            }
        }
    }

    pub fn insert_path_abstate(
        &mut self,
        path_index: usize,
        place: usize,
        abitem: AbstractStateItem<'tcx>,
    ) {
        self.abstract_states
            .entry(path_index)
            .or_insert_with(|| PathInfo {
                state_map: HashMap::new(),
            })
            .state_map
            .insert(place, abitem);
    }

    pub fn set_constraint(&mut self, constraint: &Vec<(Place<'tcx>, Place<'tcx>, BinOp)>) {
        for (p1, p2, op) in constraint {
            let p1_num = self.handle_proj(false, p1.clone());
            let p2_num = self.handle_proj(false, p2.clone());
            self.chains.insert_patial_op(p1_num, p2_num, op);

            if let BinOp::Eq = op {
                let maybe_const = self.value_domains.get(&p2_num).and_then(|d| {
                    if let Some(SymbolicDef::Constant(c)) = d.def {
                        Some(c)
                    } else {
                        None
                    }
                });

                if let Some(c) = maybe_const {
                    self.value_domains
                        .entry(p1_num)
                        .and_modify(|d| d.value_constraint = Some(c))
                        .or_insert(ValueDomain {
                            def: None,
                            value_constraint: Some(c),
                            align: None,
                        });
                }

                let maybe_const_p1 = self.value_domains.get(&p1_num).and_then(|d| {
                    if let Some(SymbolicDef::Constant(c)) = d.def {
                        Some(c)
                    } else {
                        None
                    }
                });

                if let Some(c) = maybe_const_p1 {
                    self.value_domains
                        .entry(p2_num)
                        .and_modify(|d| d.value_constraint = Some(c))
                        .or_insert(ValueDomain {
                            def: None,
                            value_constraint: Some(c),
                            align: None,
                        });
                }
            }
        }
    }

    pub fn get_layout_by_place_usize(&self, place: usize) -> PlaceTy<'tcx> {
        if let Some(ty) = self.chains.get_obj_ty_through_chain(place) {
            return self.visit_ty_and_get_layout(ty);
        } else {
            return PlaceTy::Unknown;
        }
    }

    pub fn visit_ty_and_get_layout(&self, ty: Ty<'tcx>) -> PlaceTy<'tcx> {
        match ty.kind() {
            TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _)
            | TyKind::Slice(ty)
            | TyKind::Array(ty, _) => self.visit_ty_and_get_layout(*ty),
            TyKind::Param(param_ty) => {
                let generic_name = param_ty.name.to_string();
                let mut layout_set: HashSet<(usize, usize)> = HashSet::new();
                let ty_set = self.generic_map.get(&generic_name.clone());
                if ty_set.is_none() {
                    if self.visit_time == 0 {
                        rap_warn!(
                            "Can not get generic type set: {:?}, def_id:{:?}",
                            generic_name,
                            self.def_id
                        );
                    }
                    return PlaceTy::GenericTy(generic_name, HashSet::new(), layout_set);
                }
                for ty in ty_set.unwrap().clone() {
                    if let PlaceTy::Ty(align, size) = self.visit_ty_and_get_layout(ty) {
                        layout_set.insert((align, size));
                    }
                }
                return PlaceTy::GenericTy(generic_name, ty_set.unwrap().clone(), layout_set);
            }
            TyKind::Adt(def, _list) => {
                if def.is_enum() {
                    return PlaceTy::Unknown;
                } else {
                    PlaceTy::Unknown
                }
            }
            TyKind::Closure(_, _) => PlaceTy::Unknown,
            TyKind::Alias(_, ty) => {
                // rap_warn!("self ty {:?}",ty.self_ty());
                return self.visit_ty_and_get_layout(ty.self_ty());
            }
            _ => {
                let param_env = self.tcx.param_env(self.def_id);
                let ty_env = ty::TypingEnv::post_analysis(self.tcx, self.def_id);
                let input = PseudoCanonicalInput {
                    typing_env: ty_env,
                    value: ty,
                };
                if let Ok(layout) = self.tcx.layout_of(input) {
                    // let layout = self.tcx.layout_of(param_env.and(ty)).unwrap();
                    let align = layout.align.abi.bytes_usize();
                    let size = layout.size.bytes() as usize;
                    return PlaceTy::Ty(align, size);
                } else {
                    // rap_warn!("Find type {:?} that can't get layout!", ty);
                    PlaceTy::Unknown
                }
            }
        }
    }

    pub fn get_abstate_by_place_in_path(
        &self,
        place: usize,
        path_index: usize,
    ) -> AbstractStateItem<'tcx> {
        if let Some(abstate) = self.abstract_states.get(&path_index) {
            if let Some(abs) = abstate.state_map.get(&place).cloned() {
                return abs;
            }
        }
        AbstractStateItem::new_default()
    }

    pub fn handle_binary_op(
        &mut self,
        first_op: &Operand,
        bin_op: &BinOp,
        second_op: &Operand,
        path_index: usize,
    ) {
        match bin_op {
            BinOp::Offset => {
                let _first_place = get_arg_place(first_op);
                let _second_place = get_arg_place(second_op);
            }
            _ => {}
        }
    }

    fn handle_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &mir::SwitchTargets,
        next_bb: usize,
    ) {
        let discr_op = match self.lift_operand(discr) {
            Some(op) => op,
            None => return,
        };

        let discr_local_idx = match discr_op {
            AnaOperand::Local(idx) => idx,
            _ => return,
        };

        let mut matched_val = None;
        for (val, target_bb) in targets.iter() {
            if target_bb.as_usize() == next_bb {
                matched_val = Some(val);
                break;
            }
        }

        if let Some(val) = matched_val {
            let constraint =
                SymbolicDef::Binary(BinOp::Eq, discr_local_idx, AnaOperand::Const(val));
            self.path_constraints.push(constraint);
        } else if targets.otherwise().as_usize() == next_bb {
            for (val, _) in targets.iter() {
                let constraint =
                    SymbolicDef::Binary(BinOp::Ne, discr_local_idx, AnaOperand::Const(val));
                self.path_constraints.push(constraint);
            }
        }
    }

    pub fn handle_proj(&mut self, is_right: bool, place: Place<'tcx>) -> usize {
        let mut proj_id = place.local.as_usize();
        for proj in place.projection {
            match proj {
                ProjectionElem::Deref => {
                    proj_id = self.chains.get_point_to_id(place.local.as_usize());
                    if proj_id == place.local.as_usize() {
                        proj_id = self.chains.check_ptr(proj_id);
                    }
                }
                ProjectionElem::Field(field, ty) => {
                    proj_id = self
                        .chains
                        .get_field_node_id(proj_id, field.as_usize(), Some(ty));
                }
                _ => {}
            }
        }
        proj_id
    }

    fn record_value_def(&mut self, local_idx: usize, def: SymbolicDef) {
        self.value_domains
            .entry(local_idx)
            .and_modify(|d| d.def = Some(def.clone()))
            .or_insert(ValueDomain {
                def: Some(def),
                value_constraint: None,
                align: None,
            });
    }

    fn lift_operand(&mut self, op: &Operand<'tcx>) -> Option<AnaOperand> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    Some(AnaOperand::Local(place.local.as_usize()))
                } else {
                    Some(AnaOperand::Local(self.handle_proj(true, place.clone())))
                }
            }
            Operand::Constant(box c) => match c.const_ {
                rustc_middle::mir::Const::Ty(_ty, const_value) => {
                    if let Some(val) = const_value.try_to_target_usize(self.tcx) {
                        Some(AnaOperand::Const(val as u128))
                    } else {
                        None
                    }
                }
                rustc_middle::mir::Const::Unevaluated(_unevaluated, _ty) => None,
                rustc_middle::mir::Const::Val(const_value, _ty) => {
                    if let Some(scalar) = const_value.try_to_scalar_int() {
                        let val = scalar.to_uint(scalar.size());
                        Some(AnaOperand::Const(val))
                    } else {
                        None
                    }
                }
            },
        }
    }
}

impl<'tcx> BodyVisitor<'tcx> {
    pub fn display_value_domains(&self) {
        println!("\n{:=^80}", " Value Domain Analysis Report ");

        let mut locals: Vec<&usize> = self.value_domains.keys().collect();
        locals.sort();

        if locals.is_empty() {
            println!("  [Empty Value Domains]");
            println!("{:=^80}\n", "");
            return;
        }

        // Table: Local(6) | Definition(40) | Constraint(15) | Alignment(12)
        let header = format!(
            "| {:^6} | {:^40} | {:^15} | {:^12} |",
            "Local", "Symbolic Definition", "Constraint", "Align"
        );
        let sep = format!("+{:-^6}+{:-^40}+{:-^15}+{:-^12}+", "", "", "", "");

        println!("{}", sep);
        println!("{}", header);
        println!("{}", sep);

        for local_idx in locals {
            let domain = &self.value_domains[local_idx];

            let local_str = format!("_{}", local_idx);
            let def_str = self.format_symbolic_def(domain.def.as_ref());
            let constraint_str = match domain.value_constraint {
                Some(v) => format!("== {}", v),
                None => String::from("-"),
            };
            let align_str = match domain.align {
                Some((a, s)) => format!("a:{}, s:{}", a, s),
                None => String::from("-"),
            };

            let def_str_display = if def_str.len() > 38 {
                format!("{}..", &def_str[..36])
            } else {
                def_str
            };

            println!(
                "| {:<6} | {:<40} | {:<15} | {:<12} |",
                local_str, def_str_display, constraint_str, align_str
            );
        }

        println!("{}", sep);
        println!("{:=^80}\n", " End Report ");
    }

    fn format_symbolic_def(&self, def: Option<&SymbolicDef>) -> String {
        match def {
            None => String::from("Top (Unknown)"),
            Some(d) => match d {
                SymbolicDef::Param(idx) => format!("Param(arg_{})", idx),
                SymbolicDef::Constant(val) => format!("Const({})", val),
                SymbolicDef::Use(idx) => format!("Copy(__{})", idx),
                SymbolicDef::Ref(idx) => format!("&__{}", idx),
                SymbolicDef::Cast(idx, ty_str) => format!("_{} as {}", idx, ty_str),
                SymbolicDef::UnOp(op) => format!("{:?}(op)", op), // 建议修改 UnOp 定义以包含操作数
                SymbolicDef::Binary(op, lhs, rhs) => {
                    let op_str = self.binop_to_symbol(op);
                    let rhs_str = match rhs {
                        AnaOperand::Local(i) => format!("_{}", i),
                        AnaOperand::Const(c) => format!("{}", c),
                    };
                    format!("_{} {} {}", lhs, op_str, rhs_str)
                }
                SymbolicDef::Call(func_name, args) => {
                    let args_str: Vec<String> = args.iter().map(|a| format!("_{}", a)).collect();
                    format!("{}({})", func_name, args_str.join(", "))
                }
            },
        }
    }

    fn binop_to_symbol(&self, op: &BinOp) -> &'static str {
        match op {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::BitXor => "^",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Offset => "ptr_offset",
            _ => "",
        }
    }
}
