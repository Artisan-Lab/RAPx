use annotate_snippets::Level;
use annotate_snippets::Renderer;
use annotate_snippets::Snippet;
use once_cell::sync::OnceCell;

use crate::analysis::core::dataflow::graph::DFSStatus;
use crate::analysis::core::dataflow::graph::Direction;
use crate::analysis::opt::OptCheck;
use rustc_hir::{intravisit, Expr, ExprKind};
use rustc_middle::mir::Local;
use rustc_middle::ty::{TyCtxt, TyKind, TypeckResults};
use rustc_span::Span;
use std::collections::HashSet;
static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

use crate::analysis::core::dataflow::graph::Graph;
use crate::analysis::core::dataflow::graph::GraphNode;
use crate::analysis::core::dataflow::graph::NodeOp;
use crate::analysis::utils::def_path::DefPath;
use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};

struct DefPaths {
    hashset_insert: DefPath,
    hashset_new: DefPath,
    clone: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            hashset_insert: DefPath::new("std::collections::HashSet::insert", tcx),
            hashset_new: DefPath::new("std::collections::HashSet::new", tcx),
            clone: DefPath::new("std::clone::Clone::clone", tcx),
        }
    }
}

struct HashSetInsertFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: HashSet<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HashSetInsertFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(_, receiver, ..) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            let target_def_id = (&DEFPATHS.get().unwrap()).hashset_insert.last_def_id();
            if def_id == target_def_id {
                let ty = self.typeck_results.node_type(receiver.hir_id);
                if let TyKind::Adt(.., generic_args) = ty.kind() {
                    // we check whether the first generic arg is a ref type
                    if !matches!(
                        generic_args.get(0).unwrap().expect_ty().kind(),
                        TyKind::Ref(..)
                    ) {
                        self.record.insert(ex.span);
                    }
                }
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

// check that the param of insert is moved from a cloned value
fn find_first_param_upside_clone(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let mut clone_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.clone.last_def_id();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == target_def_id {
                    clone_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    graph.dfs(
        graph.edges[node.in_edges[1]].src, // the first param is self, so we use 1
        Direction::Upside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
    );
    clone_node_idx
}

// find the upside "new" node of the "insert" node if it exists
fn find_hashset_new_node(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let mut new_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.hashset_new.last_def_id();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == target_def_id {
                    new_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    graph.dfs(
        graph.edges[node.in_edges[0]].src, // the first param is self
        Direction::Upside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
    );
    new_node_idx
}

fn report_hash_key_cloning(graph: &Graph, clone_span: Span, insert_span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(clone_span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, clone_span))
                .label("Cloning happens here."),
        )
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, insert_span))
                .label("Used here."),
        );
    let message = Level::Warning
        .title("Unnecessary memory cloning detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use borrowings as keys."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}

pub struct HashKeyCloningCheck {
    record: Vec<(Span, Span)>,
}

impl OptCheck for HashKeyCloningCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir().body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let mut hashset_finder = HashSetInsertFinder {
            typeck_results,
            record: HashSet::new(),
        };
        intravisit::walk_body(&mut hashset_finder, body);
        for node in graph.nodes.iter() {
            if hashset_finder.record.contains(&node.span) {
                if let Some(clone_node_idx) = find_first_param_upside_clone(graph, node) {
                    if let Some(new_node_idx) = find_hashset_new_node(graph, node) {
                        if !graph.is_connected(new_node_idx, Local::from_usize(0)) {
                            let clone_span = graph.nodes[clone_node_idx].span;
                            self.record.push((clone_span, node.span));
                        }
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (clone_span, insert_span) in self.record.iter() {
            report_hash_key_cloning(graph, *clone_span, *insert_span);
        }
    }
}
