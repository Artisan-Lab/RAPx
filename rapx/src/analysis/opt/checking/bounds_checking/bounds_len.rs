use once_cell::sync::OnceCell;

use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;

use crate::analysis::core::dataflow::graph::{
    AggKind, DFSStatus, Direction, Graph, GraphNode, NodeOp,
};
use crate::analysis::utils::def_path::DefPath;
use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};
use annotate_snippets::{Level, Renderer, Snippet};

use super::super::super::NO_STD;

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    ops_range: DefPath,
    vec_len: DefPath,
    ops_index: DefPath,
    ops_index_mut: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        let no_std = NO_STD.lock().unwrap();
        if *no_std {
            Self {
                ops_range: DefPath::new("core::ops::Range", tcx),
                vec_len: DefPath::new("alloc::vec::Vec::len", tcx),
                ops_index: DefPath::new("core::ops::Index::index", tcx),
                ops_index_mut: DefPath::new("core::ops::IndexMut::index_mut", tcx),
            }
        } else {
            Self {
                ops_range: DefPath::new("std::ops::Range", tcx),
                vec_len: DefPath::new("std::vec::Vec::len", tcx),
                ops_index: DefPath::new("std::ops::Index::index", tcx),
                ops_index_mut: DefPath::new("std::ops::IndexMut::index_mut", tcx),
            }
        }
    }
}

use crate::analysis::opt::OptCheck;

pub struct BoundsLenCheck {
    record: Vec<(Local, Vec<Local>)>,
}

impl OptCheck for BoundsLenCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for (node_idx, node) in graph.nodes.iter_enumerated() {
            if let Some(upperbound_node_idx) = extract_upperbound_node_if_ops_range(graph, node) {
                if let Some(vec_len_node_idx) = find_upside_vec_len_node(graph, upperbound_node_idx)
                {
                    let maybe_vec_node_idx = graph.get_upside_idx(vec_len_node_idx, 0).unwrap();
                    let maybe_vec_node_idxs =
                        graph.collect_equivalent_locals(maybe_vec_node_idx, true);
                    let mut index_record = Vec::new();
                    for index_node_idx in find_downside_index_node(graph, node_idx).into_iter() {
                        let maybe_vec_node_idx = graph.get_upside_idx(index_node_idx, 0).unwrap();
                        if maybe_vec_node_idxs.contains(&maybe_vec_node_idx) {
                            index_record.push(index_node_idx);
                        }
                    }
                    if !index_record.is_empty() {
                        self.record.push((upperbound_node_idx, index_record));
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (upperbound_node_idx, index_record) in self.record.iter() {
            report_upperbound_bug(graph, *upperbound_node_idx, index_record);
        }
    }
}

fn extract_upperbound_node_if_ops_range(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.ops_range.last_def_id();
    for op in node.ops.iter() {
        if let NodeOp::Aggregate(AggKind::Adt(def_id)) = op {
            if *def_id == target_def_id {
                let upperbound_edge = &graph.edges[node.in_edges[1]]; // the second field
                return Some(upperbound_edge.src);
            }
        }
    }
    None
}

fn find_upside_vec_len_node(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut vec_len_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.vec_len.last_def_id();
    // Warning: may traverse all upside nodes and the new result will overwrite on the previous result
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == target_def_id {
                    vec_len_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    graph.dfs(
        node_idx,
        Direction::Upside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
    );
    vec_len_node_idx
}

fn find_downside_index_node(graph: &Graph, node_idx: Local) -> Vec<Local> {
    let mut index_node_idxs: Vec<Local> = Vec::new();
    let def_paths = &DEFPATHS.get().unwrap();
    // Warning: traverse all downside nodes
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.ops_index.last_def_id()
                    || *def_id == def_paths.ops_index_mut.last_def_id()
                {
                    index_node_idxs.push(idx);
                    break;
                }
            }
        }
        DFSStatus::Continue
    };
    graph.dfs(
        node_idx,
        Direction::Downside,
        &mut node_operator,
        &mut Graph::always_true_edge_validator,
        true,
    );
    index_node_idxs
}

fn report_upperbound_bug(graph: &Graph, upperbound_node_idx: Local, index_record: &Vec<Local>) {
    let upperbound_span = graph.nodes[upperbound_node_idx].span;
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(upperbound_span);
    let mut snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Info
                .span(relative_pos_range(graph.span, upperbound_span))
                .label("Index is upperbounded."),
        );
    for node_idx in index_record {
        let index_span = graph.nodes[*node_idx].span;
        snippet = snippet.annotation(
            Level::Error
                .span(relative_pos_range(graph.span, index_span))
                .label("Checked here."),
        );
    }
    let message = Level::Warning
        .title("Unnecessary bounds checkings detected")
        .snippet(snippet);
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
