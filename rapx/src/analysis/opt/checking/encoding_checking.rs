use once_cell::sync::OnceCell;

use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::analysis::core::dataflow::graph::{
    DFSStatus, Direction, EdgeIdx, EdgeOp, Graph, GraphNode, NodeOp,
};
use crate::analysis::utils::def_path::DefPath;
use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};
use annotate_snippets::{Level, Renderer, Snippet};

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    string_from_utf8: DefPath,
    string_from_utf8_lossy: DefPath,
    vec_new: DefPath,
    vec_push: DefPath,
}

impl DefPaths {
    // only supports push operation (can't support direct assignment)
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            string_from_utf8: DefPath::new("std::string::String::from_utf8", tcx),
            string_from_utf8_lossy: DefPath::new("std::string::String::from_utf8_lossy", tcx),
            vec_new: DefPath::new("std::vec::Vec::new", tcx),
            vec_push: DefPath::new("std::vec::Vec::push", tcx),
        }
    }
}

use crate::analysis::opt::OptCheck;

pub struct EncodingCheck {
    record: Vec<Span>,
}

fn extract_vec_if_is_string_from(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.string_from_utf8.last_def_id()
                || *def_id == def_paths.string_from_utf8_lossy.last_def_id()
            {
                let in_edge = &graph.edges[node.in_edges[0]];
                return Some(in_edge.src);
            }
        }
    }
    None
}

fn find_upside_vec_new_node(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut vec_new_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let target_def_id = def_paths.vec_new.last_def_id();
    // Warning: may traverse all upside nodes and the new result will overwrite on the previous result
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == target_def_id {
                    vec_new_node_idx = Some(idx);
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
        &mut Graph::always_true_edge_validator,
        false,
    );
    vec_new_node_idx
}

// todo: we can find downside index node too

fn find_downside_push_node(graph: &Graph, node_idx: Local) -> Vec<Local> {
    let mut push_node_idxs: Vec<Local> = Vec::new();
    let def_paths = &DEFPATHS.get().unwrap();
    // Warning: traverse all downside nodes
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.vec_push.last_def_id() {
                    push_node_idxs.push(idx);
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
    push_node_idxs
}

// Warning: WE APPROXIMATELY VIEW CONST U8s AS SAFE INPUT
// which may cause wrong result.

// todo: ascii chars are extracted from String variables
fn value_pushed_is_from_const(graph: &Graph, vec_push_idx: Local) -> bool {
    let mut const_found = false;
    let pushed_value_edge = &graph.edges[graph.nodes[vec_push_idx].in_edges[1]]; // The second parameter
    let pushed_value_idx = pushed_value_edge.src;
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Const(desc) = op {
                if desc.contains("u8") {
                    const_found = true;
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut edge_validator = |graph: &Graph, idx: EdgeIdx| {
        let edge = &graph.edges[idx];
        let dst_node = &graph.nodes[edge.dst];
        match dst_node.in_edges.len() {
            1 => Graph::always_true_edge_validator(graph, idx),
            2 => {
                if let EdgeOp::Index = edge.op {
                    DFSStatus::Continue
                } else {
                    DFSStatus::Stop
                }
            }
            _ => DFSStatus::Stop,
        }
    };
    graph.dfs(
        pushed_value_idx,
        Direction::Upside,
        &mut node_operator,
        &mut edge_validator,
        false,
    );
    const_found
}

impl OptCheck for EncodingCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if let Some(vec_node_idx) = extract_vec_if_is_string_from(graph, node) {
                if let Some(vec_new_idx) = find_upside_vec_new_node(graph, vec_node_idx) {
                    let vec_push_indice = find_downside_push_node(graph, vec_new_idx);
                    for vec_push_idx in vec_push_indice {
                        if !value_pushed_is_from_const(graph, vec_push_idx) {
                            self.record.clear();
                            return;
                        }
                    }
                    self.record.push(node.span);
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_encoding_bug(graph, *span);
        }
    }
}

fn report_encoding_bug(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(graph.span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Checked here."),
        );
    let message = Level::Warning
        .title("Unnecessary encoding checkings detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use unsafe APIs."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
