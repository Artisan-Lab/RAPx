use crate::analysis::core::alias::FnMap;
use crate::analysis::safedrop::graph::SafeDropGraph;
use crate::analysis::utils::fn_info::display_hashmap;
use crate::analysis::utils::fn_info::get_all_std_unsafe_callees_block_id;
use crate::analysis::utils::fn_info::get_callees;
use crate::analysis::utils::fn_info::get_cleaned_def_path_name;
use crate::analysis::utils::fn_info::is_ptr;
use crate::analysis::utils::fn_info::is_ref;
use crate::analysis::utils::show_mir::display_mir;
use crate::rap_warn;
use rustc_middle::mir::Local;
use rustc_middle::mir::ProjectionElem;
use rustc_middle::ty::PseudoCanonicalInput;
use rustc_span::source_map::Spanned;
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::contracts::abstract_state::{
    AbstractStateItem, AlignState, PathInfo, StateType, VType, Value,
};
use super::contracts::contract::Contract;
use super::dominated_chain::DominatedGraph;
use super::generic_check::GenericChecker;
use super::inter_record::InterAnalysisRecord;
use super::matcher::UnsafeApi;
use super::matcher::{get_arg_place, parse_unsafe_api};
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
    pub paths: Vec<Vec<usize>>,
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
            proj_ty: HashMap::new(),
            chains: DominatedGraph::new(tcx, def_id),
            paths: Vec::new(),
        }
    }

    pub fn get_ty_by_place(&self, p: usize) -> Ty<'tcx> {
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        return locals[Local::from(p)].ty;
    }

    pub fn path_forward_check(&mut self, fn_map: &FnMap) {
        if self.visit_time >= 1000 {
            return;
        }
        let paths: Vec<Vec<usize>> = self.get_all_paths();
        self.paths = paths.clone();
        if self.visit_time == 0 {
            // rap_warn!("{:?}",self.chains.variables);
        }
        let body = self.tcx.optimized_mir(self.def_id);

        // initialize local vars' types
        let locals = body.local_decls.clone();
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            let layout = self.visit_ty_and_get_layout(local_ty);
            self.local_ty.insert(idx, layout);
        }

        // Iterate all the paths. Paths have been handled by tarjan.
        for (index, path_info) in paths.iter().enumerate() {
            self.chains = DominatedGraph::new(self.tcx, self.def_id);
            self.chains.init_arg();
            self.abstract_states.insert(index, PathInfo::new());
            for block_index in path_info.iter() {
                if block_index >= &body.basic_blocks.len() {
                    continue;
                }
                self.path_analyze_block(
                    &body.basic_blocks[BasicBlock::from_usize(*block_index)].clone(),
                    index,
                    *block_index,
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
                            fn_map,
                        );
                    }
                }
            }
            // if self.visit_time == 0 {
            //     rap_warn!("In path {index}");
            //     display_hashmap(&self.chains.variables, 1);
            // }
        }
    }

    pub fn path_analyze_block(
        &mut self,
        block: &BasicBlockData<'tcx>,
        path_index: usize,
        bb_index: usize,
        fn_map: &FnMap,
    ) {
        for statement in block.statements.iter() {
            self.path_analyze_statement(statement, path_index);
        }
        self.path_analyze_terminator(&block.terminator(), path_index, bb_index, fn_map);
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
            StatementKind::StorageDead(local) => {
                // self.chains.delete_node(local.as_usize());
            }
            _ => {}
        }
    }

    pub fn path_analyze_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        path_index: usize,
        bb_index: usize,
        fn_map: &FnMap,
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
                    if let ty::FnDef(ref callee_def_id, raw_list) = func_constant.const_.ty().kind()
                    {
                        self.handle_call(
                            dst_place,
                            callee_def_id,
                            args,
                            path_index,
                            fn_map,
                            *fn_span,
                        );
                    }
                }
            }
            TerminatorKind::Drop {
                place,
                target,
                unwind: _,
                replace: _,
            } => {
                let drop_local = self.handle_proj(false, *place);
                if !self.chains.set_drop(drop_local) {
                    // rap_warn!(
                    //     "In path {:?}, double drop {drop_local} in block {bb_index}",
                    //     self.paths[path_index]
                    // );
                }
            }
            _ => {}
        }
    }

    pub fn path_analyze_assign(
        &mut self,
        lplace: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        path_index: usize,
    ) {
        let lpjc_local = self.handle_proj(false, lplace.clone());
        match rvalue {
            Rvalue::Use(op) => match op {
                Operand::Move(rplace) => {
                    let rpjc_local = self.handle_proj(true, rplace.clone());
                    self.chains.merge(lpjc_local, rpjc_local);
                }
                Operand::Copy(rplace) => {
                    let rpjc_local = self.handle_proj(true, rplace.clone());
                    self.chains.copy_node(lpjc_local, rpjc_local);
                }
                _ => {}
            },
            Rvalue::Repeat(op, _const) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local = self.handle_proj(true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::Ref(_, _, rplace) | Rvalue::RawPtr(_, rplace) => {
                let rpjc_local = self.handle_proj(true, rplace.clone());
                // self.chains.insert_node(lpjc_local, self.chains.get_local_ty_by_place(lpjc_local));
                self.chains.point(lpjc_local, rpjc_local);
            }
            Rvalue::Cast(cast_kind, op, ty) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let rpjc_local = self.handle_proj(true, rplace.clone());
                    self.chains.point(lpjc_local, rpjc_local);
                    self.handle_cast(rpjc_local, lpjc_local, ty, path_index, cast_kind);
                }
                _ => {}
            },
            Rvalue::BinaryOp(_bin_op, box (ref _op1, ref _op2)) => {}
            Rvalue::ShallowInitBox(op, _ty) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local = self.handle_proj(true, rplace.clone());
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
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        args: &Box<[Spanned<Operand>]>,
        path_index: usize,
        fn_map: &FnMap,
        fn_span: Span,
    ) {
        if !self.tcx.is_mir_available(def_id) {
            self.insert_path_abstate(
                path_index,
                dst_place.local.as_usize(),
                AbstractStateItem::new_default(),
            );
            return;
        }

        // Find std unsafe API call, then check the contracts.
        if let Some(fn_result) =
            parse_unsafe_api(get_cleaned_def_path_name(self.tcx, *def_id).as_str())
        {
            self.handle_std_unsafe_call(
                dst_place, def_id, args, path_index, fn_map, fn_span, fn_result,
            );
        }

        // merge alias results
        self.handle_ret_alias(dst_place, def_id, fn_map, args);

        // to be deleted!
        // get pre analysis state
        let mut pre_analysis_state = HashMap::new();
        for (idx, arg) in args.iter().enumerate() {
            let arg_place = get_arg_place(&arg.node);
            let ab_state_item = self.get_abstate_by_place_in_path(arg_place.1, path_index);
            pre_analysis_state.insert(idx, ab_state_item);
        }

        // check cache and update new states for args and return value
        let mut gr = self.global_recorder.clone();
        if let Some(record) = gr.get_mut(def_id) {
            if record.is_pre_state_same(&pre_analysis_state) {
                self.update_post_state(&record.post_analysis_state, args, path_index);
                self.insert_path_abstate(
                    path_index,
                    dst_place.local.as_usize(),
                    record.ret_state.clone(),
                );
                return;
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
        inter_body_visitor.path_forward_check(fn_map);
        let post_analysis_state: HashMap<usize, AbstractStateItem<'_>> =
            inter_body_visitor.get_args_post_states().clone();
        self.update_post_state(&post_analysis_state, args, path_index);
        let ret_state = post_analysis_state.get(&0).unwrap().clone();
        self.global_recorder.insert(
            *def_id,
            InterAnalysisRecord::new(pre_analysis_state, post_analysis_state, ret_state),
        );
    }

    // Use the alias analysis to support quick merge inter analysis results.
    pub fn handle_ret_alias(
        &mut self,
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        fn_map: &FnMap,
        args: &Box<[Spanned<Operand>]>,
    ) {
        let d_local = self.handle_proj(false, dst_place.clone());
        // Find alias relationship in cache.
        // If one of the op is ptr, then alias the pointed node with another.
        if let Some(retalias) = fn_map.get(def_id) {
            for alias_set in retalias.aliases() {
                let (l, r) = (alias_set.left_index, alias_set.right_index);
                let (l_fields, r_fields) = (
                    alias_set.left_field_seq.clone(),
                    alias_set.right_field_seq.clone(),
                );
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
                let is_fst_ptr = fst_to != fst_var;
                let is_snd_ptr = snd_to != snd_var;
                match (is_fst_ptr, is_snd_ptr) {
                    (false, true) => {
                        self.chains.merge(snd_to, fst_to);
                    }
                    _ => {
                        self.chains.merge(fst_to, snd_to);
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

    // if inter analysis's params are in mut_ref, then we should update their post states
    pub fn update_post_state(
        &mut self,
        post_state: &HashMap<usize, AbstractStateItem<'tcx>>,
        args: &Box<[Spanned<Operand>]>,
        path_index: usize,
    ) {
        for (idx, arg) in args.iter().enumerate() {
            let arg_place = get_arg_place(&arg.node);
            if let Some(state_item) = post_state.get(&idx) {
                self.insert_path_abstate(path_index, arg_place.1, state_item.clone());
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

    pub fn get_all_paths(&mut self) -> Vec<Vec<usize>> {
        self.safedrop_graph.solve_scc();
        let mut results: Vec<Vec<usize>> = self.safedrop_graph.get_paths();
        let contains_unsafe_blocks = get_all_std_unsafe_callees_block_id(self.tcx, self.def_id);
        results.retain(|path| {
            path.iter()
                .any(|block_id| contains_unsafe_blocks.contains(block_id))
        });
        results
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
                let generic_name = param_ty.name.as_str().to_string();
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
                    rap_warn!("Find type {:?} that can't get layout!", ty);
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
        return AbstractStateItem::new_default();
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
                let r_abitem = self.get_abstate_by_place_in_path(rpjc_local, path_index);
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

                let dst_ty = self.visit_ty_and_get_layout(*ty);
                let align_state =
                    StateType::AlignState(AlignState::Cast(src_ty.clone(), dst_ty.clone()));
                let abitem = AbstractStateItem::new(
                    (Value::None, Value::None),
                    VType::Pointer(dst_ty),
                    HashSet::from([align_state]),
                );
                self.insert_path_abstate(path_index, lpjc_local, abitem);
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
                let _first_place = get_arg_place(first_op);
                let _second_place = get_arg_place(second_op);
            }
            _ => {}
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
}
