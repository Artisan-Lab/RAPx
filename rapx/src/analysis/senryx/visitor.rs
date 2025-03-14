use crate::analysis::safedrop::graph::SafeDropGraph;
use crate::analysis::utils::fn_info::get_cleaned_def_path_name;
use crate::analysis::utils::show_mir::display_mir;
use crate::{rap_error, rap_warn};
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::contracts::abstract_state::{
    AbstractState, AbstractStateItem, AlignState, StateType, VType, Value,
};
use super::contracts::contract::Contract;
use super::generic_check::GenericChecker;
use super::inter_record::InterAnalysisRecord;
use super::matcher::{get_arg_place, match_unsafe_api_and_check_contracts};
use crate::analysis::core::heap_item::AdtOwner;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    mir::{
        self, AggregateKind, BasicBlock, BasicBlockData, BinOp, CastKind, Operand, Place, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{self, GenericArgKind, Ty, TyKind},
};

//TODO: modify contracts vec to contract-bool pairs (we can also use path index to record path info)
pub struct CheckResult<'tcx> {
    pub func_name: String,
    pub func_span: Span,
    pub failed_contracts: Vec<(usize, Contract<'tcx>)>,
    pub passed_contracts: Vec<(usize, Contract<'tcx>)>,
}

impl<'tcx> CheckResult<'tcx> {
    pub fn new(func_name: &str, func_span: Span) -> Self {
        Self {
            func_name: func_name.to_string(),
            func_span,
            failed_contracts: Vec::new(),
            passed_contracts: Vec::new(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PlaceTy<'tcx> {
    Ty(usize, usize), // layout(align,size) of one specific type
    GenericTy(String, HashSet<Ty<'tcx>>, HashSet<(usize, usize)>), // get specific type in generic map
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
    pub abstract_states: HashMap<usize, AbstractState<'tcx>>,
    pub unsafe_callee_report: HashMap<String, usize>,
    pub local_ty: HashMap<usize, PlaceTy<'tcx>>,
    pub visit_time: usize,
    pub check_results: Vec<CheckResult<'tcx>>,
    pub generic_map: HashMap<String, HashSet<Ty<'tcx>>>,
    pub global_recorder: HashMap<DefId, InterAnalysisRecord<'tcx>>,
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
        Self {
            tcx,
            def_id,
            safedrop_graph: SafeDropGraph::new(body, tcx, def_id, AdtOwner::default()),
            abstract_states: HashMap::new(),
            unsafe_callee_report: HashMap::new(),
            local_ty: HashMap::new(),
            visit_time,
            check_results: Vec::new(),
            generic_map: satisfied_ty_map_for_generic,
            global_recorder,
        }
    }

    pub fn path_forward_check(&mut self) {
        let paths = self.get_all_paths();
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            let layout = self.visit_ty_and_get_layout(local_ty);
            self.local_ty.insert(idx, layout);
        }

        // display_mir(self.def_id,&body);
        for (index, path_info) in paths.iter().enumerate() {
            self.abstract_states.insert(index, AbstractState::new());
            for block_index in path_info.iter() {
                if block_index >= &body.basic_blocks.len() {
                    continue;
                }
                self.path_analyze_block(
                    &body.basic_blocks[BasicBlock::from_usize(*block_index)].clone(),
                    index,
                    *block_index,
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
                        );
                    }
                }
            }
        }
        // self.abstract_states_mop();
        // self.abstate_debug();
    }

    pub fn path_analyze_block(
        &mut self,
        block: &BasicBlockData<'tcx>,
        path_index: usize,
        bb_index: usize,
    ) {
        for statement in block.statements.iter() {
            self.path_analyze_statement(statement, path_index);
        }
        self.path_analyze_terminator(&block.terminator(), path_index, bb_index);
    }

    pub fn path_analyze_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        path_index: usize,
        _bb_index: usize,
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination: _,
                target: _,
                unwind: _,
                call_source: _,
                fn_span,
            } => {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(ref callee_def_id, raw_list) = func_constant.const_.ty().kind()
                    {
                        let func_name = get_cleaned_def_path_name(self.tcx, *callee_def_id);
                        if self.visit_time == 0 {
                            for generic_arg in raw_list.iter() {
                                match generic_arg.unpack() {
                                    GenericArgKind::Type(ty) => {
                                        if let Some(new_check_result) =
                                            match_unsafe_api_and_check_contracts(
                                                func_name.as_str(),
                                                args,
                                                &self.abstract_states.get(&path_index).unwrap(),
                                                *fn_span,
                                                ty,
                                            )
                                        {
                                            if let Some(_existing) =
                                                self.check_results.iter_mut().find(|result| {
                                                    result.func_name == new_check_result.func_name
                                                })
                                            {
                                            } else {
                                                self.check_results.push(new_check_result);
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        self.handle_call(callee_def_id, args, path_index);
                    }
                }
            }
            _ => {}
        }
    }

    pub fn path_analyze_statement(&mut self, statement: &Statement<'tcx>, _path_index: usize) {
        match statement.kind {
            StatementKind::Assign(box (ref lplace, ref rvalue)) => {
                self.path_analyze_assign(lplace, rvalue, _path_index);
            }
            StatementKind::Intrinsic(box ref intrinsic) => match intrinsic {
                mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                    if cno.src.place().is_some() && cno.dst.place().is_some() {
                        let _src_pjc_local = self.safedrop_graph.projection(
                            self.tcx,
                            true,
                            cno.src.place().unwrap().clone(),
                        );
                        let _dst_pjc_local = self.safedrop_graph.projection(
                            self.tcx,
                            true,
                            cno.dst.place().unwrap().clone(),
                        );
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }

    pub fn path_analyze_assign(
        &mut self,
        lplace: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        path_index: usize,
    ) {
        let lpjc_local = self
            .safedrop_graph
            .projection(self.tcx, false, lplace.clone());
        match rvalue {
            Rvalue::Use(op) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let rpjc_local = self
                        .safedrop_graph
                        .projection(self.tcx, true, rplace.clone());
                    if let Some(ab_state) = self.abstract_states.get(&path_index) {
                        if let Some(r_state_item) = ab_state.state_map.get(&rpjc_local) {
                            self.insert_path_abstate(path_index, lpjc_local, r_state_item.clone());
                        }
                    }
                }
                _ => {}
            },
            Rvalue::Repeat(op, _const) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local =
                        self.safedrop_graph
                            .projection(self.tcx, true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::Ref(_, _, rplace) => {
                let rpjc_local = self
                    .safedrop_graph
                    .projection(self.tcx, true, rplace.clone());
                let ty = self.get_layout_by_place_usize(rpjc_local);
                let abitem = AbstractStateItem::new(
                    (Value::None, Value::None),
                    VType::Pointer(ty),
                    HashSet::from([StateType::AlignState(AlignState::Aligned)]),
                );
                self.insert_path_abstate(path_index, lpjc_local, Some(abitem));
            }
            Rvalue::Cast(cast_kind, op, ty) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let rpjc_local = self
                        .safedrop_graph
                        .projection(self.tcx, true, rplace.clone());
                    self.handle_cast(rpjc_local, lpjc_local, ty, path_index, cast_kind);
                }
                _ => {}
            },
            Rvalue::BinaryOp(_bin_op, box (ref _op1, ref _op2)) => {}
            Rvalue::ShallowInitBox(op, _ty) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local =
                        self.safedrop_graph
                            .projection(self.tcx, true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::Aggregate(box ref agg_kind, _op_vec) => match agg_kind {
                AggregateKind::Array(_ty) => {}
                _ => {}
            },
            Rvalue::Discriminant(_place) => {
                // println!("Discriminant {}:{:?}",lpjc_local,rvalue);
            }
            _ => {}
        }
    }

    pub fn handle_call(
        &mut self,
        def_id: &DefId,
        args: &Box<[Spanned<Operand>]>,
        path_index: usize,
    ) {
        if !self.tcx.is_mir_available(def_id) {
            return;
        }
        // get pre analysis state
        let mut pre_analysis_state = HashMap::new();
        for (idx, arg) in args.iter().enumerate() {
            let arg_place = get_arg_place(&arg.node);
            let ab_state_item = self.get_abstate_by_place_in_path(arg_place, path_index);
            pre_analysis_state.insert(idx, ab_state_item);
        }

        // check cache
        let mut gr = self.global_recorder.clone();
        if let Some(record) = gr.get_mut(def_id) {
            if record.is_pre_state_same(&pre_analysis_state) {
                self.update_post_state(&record.post_analysis_state, args, path_index);
            }
        }

        // update post states and cache
        let tcx = self.tcx;
        let mut inter_body_visitor: BodyVisitor<'_> = BodyVisitor::new(
            tcx,
            *def_id,
            self.global_recorder.clone(),
            self.visit_time + 1,
        );
        inter_body_visitor.path_forward_check();
        let post_analysis_state: HashMap<usize, Option<AbstractStateItem<'_>>> =
            inter_body_visitor.get_args_post_states().clone();
        // self.update_post_state(&post_analysis_state, args, path_index);
        self.global_recorder.insert(
            *def_id,
            InterAnalysisRecord::new(pre_analysis_state, post_analysis_state),
        );
    }

    // if inter analysis's params are in mut_ref, then we should update their post states
    pub fn update_post_state(
        &mut self,
        post_state: &HashMap<usize, Option<AbstractStateItem<'tcx>>>,
        args: &Box<[Spanned<Operand>]>,
        path_index: usize,
    ) {
        for (idx, arg) in args.iter().enumerate() {
            let arg_place = get_arg_place(&arg.node);
            if let Some(state_item) = post_state.get(&idx) {
                self.insert_path_abstate(path_index, arg_place, state_item.clone());
            }
        }
    }

    pub fn get_args_post_states(&mut self) -> HashMap<usize, Option<AbstractStateItem<'tcx>>> {
        let tcx = self.tcx;
        let def_id = self.def_id;
        let final_states = self.abstract_states_mop();
        let mut result_states = HashMap::new();
        let fn_sig = tcx.fn_sig(def_id).skip_binder();
        let num_params = fn_sig.inputs().skip_binder().len();
        for i in 0..num_params {
            if let Some(state) = final_states.state_map.get(&(i + 1)) {
                result_states.insert(i, state.clone());
            } else {
                result_states.insert(i, None);
            }
        }
        result_states
    }

    pub fn get_all_paths(&mut self) -> Vec<Vec<usize>> {
        self.safedrop_graph.solve_scc();
        let results = self.safedrop_graph.get_paths();
        results
    }

    pub fn abstract_states_mop(&mut self) -> AbstractState<'tcx> {
        let mut result_state = AbstractState {
            state_map: HashMap::new(),
        };

        for (_path_idx, abstract_state) in &self.abstract_states {
            for (var_index, state_item) in &abstract_state.state_map {
                if let Some(existing_state_item) = result_state.state_map.get_mut(&var_index) {
                    if existing_state_item.is_none() || state_item.is_none() {
                        continue;
                    }
                    existing_state_item
                        .clone()
                        .unwrap()
                        .meet_state_item(&state_item.clone().unwrap());
                } else {
                    result_state
                        .state_map
                        .insert(*var_index, state_item.clone());
                }
            }
        }
        result_state
    }

    pub fn abstate_debug(&self) {
        if self.visit_time != 0 {
            return;
        }
        // Self::display_hashmap(&self.local_ty, 1);
        display_mir(self.def_id, self.tcx.optimized_mir(self.def_id));
        println!("---------------");
        println!("--def_id: {:?}", self.def_id);

        let mut sorted_states: Vec<_> = self.abstract_states.iter().collect();
        sorted_states.sort_by(|a, b| a.0.cmp(b.0));
        for (path, abstract_state) in &sorted_states {
            println!("--Path-{:?}:", path);
            let mut sorted_state_map: Vec<_> = abstract_state.state_map.iter().collect();
            sorted_state_map.sort_by_key(|&(place, _)| place);
            for (place, ab_item) in sorted_state_map {
                println!("Place-{:?} has abstract states:{:?}", place, ab_item);
            }
        }
    }

    pub fn get_all_callees(&self, def_id: DefId) -> Vec<String> {
        let mut results = Vec::new();
        let body = self.tcx.optimized_mir(def_id);
        let bb_len = body.basic_blocks.len();
        for i in 0..bb_len {
            let callees = Self::get_terminator_callee(
                body.basic_blocks[BasicBlock::from_usize(i)]
                    .clone()
                    .terminator(),
            );
            results.extend(callees);
        }
        results
    }

    pub fn get_terminator_callee(terminator: &Terminator<'tcx>) -> Vec<String> {
        let mut results = Vec::new();
        match &terminator.kind {
            TerminatorKind::Call { func, .. } => {
                let func_name = format!("{:?}", func);
                results.push(func_name);
            }
            _ => {}
        }
        results
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
        abitem: Option<AbstractStateItem<'tcx>>,
    ) {
        self.abstract_states
            .entry(path_index)
            .or_insert_with(|| AbstractState {
                state_map: HashMap::new(),
            })
            .state_map
            .insert(place, abitem);
    }

    pub fn get_layout_by_place_usize(&self, place: usize) -> PlaceTy<'tcx> {
        self.local_ty.get(&place).unwrap().clone()
    }

    pub fn visit_ty_and_get_layout(&self, ty: Ty<'tcx>) -> PlaceTy<'tcx> {
        match ty.kind() {
            TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _)
            | TyKind::Slice(ty)
            | TyKind::Array(ty, _) => self.visit_ty_and_get_layout(*ty),
            TyKind::Param(param_ty) => {
                let generic_name = param_ty.name.as_str().to_string();
                let mut layout_set: HashSet<(usize, usize)> = HashSet::new();
                let ty_set = self.generic_map.get(&generic_name.clone());
                if ty_set.is_none() {
                    rap_error!("Can not get generic type set: {:?}", ty_set);
                }
                for ty in ty_set.unwrap().clone() {
                    if let PlaceTy::Ty(align, size) = self.visit_ty_and_get_layout(ty) {
                        layout_set.insert((align, size));
                    }
                }
                return PlaceTy::GenericTy(generic_name, ty_set.unwrap().clone(), layout_set);
            }
            _ => {
                let param_env = self.tcx.param_env(self.def_id);
                if let Ok(_) = self.tcx.layout_of(param_env.and(ty)) {
                    let layout = self.tcx.layout_of(param_env.and(ty)).unwrap();
                    let align = layout.align.abi.bytes_usize();
                    let size = layout.size.bytes() as usize;
                    return PlaceTy::Ty(align, size);
                } else {
                    rap_error!("Find type {:?} that can't get layout!", ty);
                    PlaceTy::Ty(0, 0)
                }
            }
        }
    }

    pub fn get_abstate_by_place_in_path(
        &self,
        place: usize,
        path_index: usize,
    ) -> Option<AbstractStateItem<'tcx>> {
        if let Some(abstate) = self.abstract_states.get(&path_index) {
            if let Some(_) = abstate.state_map.get(&place).cloned() {
                return abstate.state_map.get(&place).cloned().unwrap();
            }
        }
        return None;
    }

    pub fn display_hashmap<K, V>(map: &HashMap<K, V>, level: usize)
    where
        K: Ord + Debug + Hash,
        V: Debug,
    {
        let indent = "  ".repeat(level);
        let mut sorted_keys: Vec<_> = map.keys().collect();
        sorted_keys.sort();

        for key in sorted_keys {
            if let Some(value) = map.get(key) {
                println!("{}{:?}: {:?}", indent, key, value);
            }
        }
    }

    pub fn handle_cast(
        &mut self,
        rpjc_local: usize,
        lpjc_local: usize,
        ty: &Ty<'tcx>,
        path_index: usize,
        cast_kind: &CastKind,
    ) {
        let mut src_ty = self.get_layout_by_place_usize(rpjc_local);
        match cast_kind {
            CastKind::PtrToPtr | CastKind::PointerCoercion(_, _) => {
                if let Some(r_abitem) = self.get_abstate_by_place_in_path(rpjc_local, path_index) {
                    for state in &r_abitem.state {
                        if let StateType::AlignState(r_align_state) = state.clone() {
                            match r_align_state {
                                AlignState::Cast(from, _to) => {
                                    src_ty = from.clone();
                                }
                                _ => {}
                            }
                        }
                    }
                }
                let dst_ty = self.visit_ty_and_get_layout(*ty);
                let align_state =
                    StateType::AlignState(AlignState::Cast(src_ty.clone(), dst_ty.clone()));
                let abitem = AbstractStateItem::new(
                    (Value::None, Value::None),
                    VType::Pointer(dst_ty),
                    HashSet::from([align_state]),
                );
                self.insert_path_abstate(path_index, lpjc_local, Some(abitem));
            }
            _ => {}
        }
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
                let first_place = self.handle_operand(first_op);
                let _second_place = self.handle_operand(second_op);
                let _abitem = self.get_abstate_by_place_in_path(first_place, path_index);
            }
            _ => {}
        }
    }

    pub fn handle_operand(&self, op: &Operand) -> usize {
        match op {
            Operand::Move(place) => place.local.as_usize(),
            Operand::Copy(place) => place.local.as_usize(),
            _ => 0,
        }
    }
}
