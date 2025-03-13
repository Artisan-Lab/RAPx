use std::io::Write;

use super::extract::extract_constraints;
use super::graph::ApiDepGraph;
use super::graph::{DepEdge, DepNode};
use crate::rap_debug;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
    BodyId, FnDecl,
};

use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;

pub struct FnVisitor<'tcx, 'a> {
    fn_cnt: usize,
    tcx: TyCtxt<'tcx>,
    funcs: Vec<DefId>,
    current_fn_did: Option<DefId>,
    graph: &'a mut ApiDepGraph<'tcx>,
}

impl<'tcx, 'a> FnVisitor<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, graph: &'a mut ApiDepGraph<'tcx>) -> FnVisitor<'tcx, 'a> {
        let fn_cnt = 0;
        let funcs = Vec::new();
        FnVisitor {
            fn_cnt,
            tcx,
            graph,
            funcs,
            current_fn_did: None,
        }
    }
    pub fn fn_cnt(&self) -> usize {
        self.fn_cnt
    }
    pub fn write_funcs<T: Write>(&self, F: &mut T) {
        for id in &self.funcs {
            write!(F, "{}\n", self.tcx.def_path_str(id)).expect("fail when write funcs");
        }
    }
}

fn get_bound_var_attr(var: ty::BoundVariableKind) -> (String, bool) {
    let name: String;
    let is_lifetime;
    match var {
        ty::BoundVariableKind::Ty(bound_ty_kind) => {
            is_lifetime = false;
            name = match bound_ty_kind {
                ty::BoundTyKind::Param(_, sym) => sym.to_string(),
                _ => "anon".to_string(),
            }
        }
        ty::BoundVariableKind::Region(bound_region_kind) => {
            is_lifetime = true;
            name = match bound_region_kind {
                ty::BoundRegionKind::BrNamed(_, name) => name.to_string(),
                _ => "anon".to_string(),
            }
        }
        ty::BoundVariableKind::Const => {
            is_lifetime = false;
            name = "anon const".to_string();
        }
    }
    (name, is_lifetime)
}

impl<'tcx, 'a> Visitor<'tcx> for FnVisitor<'tcx, 'a> {
    fn visit_fn<'v>(
        &mut self,
        fk: FnKind<'v>,
        fd: &'v FnDecl<'v>,
        b: BodyId,
        span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        let fn_def_id = id.to_def_id();
        self.fn_cnt += 1;
        self.funcs.push(fn_def_id);
        let api_node = self.graph.get_node(DepNode::api(id));

        let early_fn_sig = self.tcx.fn_sig(fn_def_id);
        let binder_fn_sig = early_fn_sig.instantiate_identity();
        let fn_sig = self
            .tcx
            .liberate_late_bound_regions(fn_def_id, binder_fn_sig);
        rap_debug!("visit {}", fn_sig);

        // add generic param def to graph
        // NOTE: generics_of query only return early bound generics
        let generics = self.tcx.generics_of(fn_def_id);
        let early_generic_count = generics.count();
        rap_debug!("early bound generic count = {}", early_generic_count);
        for i in 0..early_generic_count {
            let generic_param_def = generics.param_at(i, self.tcx);
            rap_debug!("early bound generic#{i}: {:?}", generic_param_def);
            let node_index = self.graph.get_node(DepNode::generic_param_def(
                fn_def_id,
                i,
                generic_param_def.name,
                !generic_param_def.kind.is_ty_or_const(),
            ));
            self.graph
                .add_edge_once(api_node, node_index, DepEdge::fn2generic());
        }

        // add late bound generic
        rap_debug!(
            "late bound generic count = {}",
            binder_fn_sig.bound_vars().len()
        );
        for (i, var) in binder_fn_sig.bound_vars().iter().enumerate() {
            rap_debug!("bound var#{i}: {var:?}");
            let (name, is_lifetime) = get_bound_var_attr(var);
            let node_index = self.graph.get_node(DepNode::generic_param_def(
                fn_def_id,
                early_generic_count + i,
                name,
                is_lifetime,
            ));
            self.graph
                .add_edge_once(api_node, node_index, DepEdge::fn2generic());
        }

        extract_constraints(fn_def_id, self.tcx);

        // add inputs/output to graph, and compute constraints based on subtyping
        for (no, input_ty) in fn_sig.inputs().iter().enumerate() {
            // let free_input_ty = input_ty.fold_with(folder)
            let input_node = self.graph.get_node(DepNode::ty(*input_ty));
            self.graph.add_edge(input_node, api_node, DepEdge::arg(no));
        }

        let output_ty = fn_sig.output();
        let output_node = self.graph.get_node(DepNode::ty(output_ty));
        self.graph.add_edge(api_node, output_node, DepEdge::ret());
        rap_debug!("exit visit_fn");
    }
}
