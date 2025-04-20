pub mod array_encoding;
pub mod vec_encoding;

use std::collections::HashSet;

use crate::analysis::core::dataflow::graph::{
    DFSStatus, Direction, EdgeIdx, EdgeOp, Graph, NodeOp,
};
use crate::analysis::opt::OptCheck;
use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};
use annotate_snippets::{Level, Renderer, Snippet};

use array_encoding::ArrayEncodingCheck;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use vec_encoding::VecEncodingCheck;

pub struct EncodingCheck {
    vec_encoding: VecEncodingCheck,
    array_encoding: ArrayEncodingCheck,
}

impl OptCheck for EncodingCheck {
    fn new() -> Self {
        Self {
            vec_encoding: VecEncodingCheck::new(),
            array_encoding: ArrayEncodingCheck::new(),
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        self.vec_encoding.check(graph, tcx);
        self.array_encoding.check(graph, tcx);
    }

    fn report(&self, graph: &Graph) {
        self.vec_encoding.report(graph);
        self.array_encoding.report(graph);
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

// Warning: WE APPROXIMATELY VIEW CONST U8s AS SAFE INPUT
// which may cause wrong result.

// todo: ascii chars are extracted from String variables
fn value_is_from_const(graph: &Graph, value_idx: Local) -> bool {
    let mut const_found = false;
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Const(_, src_ty) = op {
                if src_ty.contains("u8") {
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
    let mut seen = HashSet::new();
    graph.dfs(
        value_idx,
        Direction::Upside,
        &mut node_operator,
        &mut edge_validator,
        false,
        &mut seen,
    );
    const_found
}
