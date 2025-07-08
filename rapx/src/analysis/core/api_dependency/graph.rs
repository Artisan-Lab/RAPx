use crate::{
    analysis::core::api_dependency::{ApiDependencyGraph, Edge, InnerGraph, Node, TyWrapper},
    utils::fs::rap_create_file,
};
use petgraph::{
    dot::{Config, Dot},
    graph::NodeIndex,
    Graph,
};

use rustc_middle::{
    query::IntoQueryParam,
    ty::{Ty, TyCtxt},
};

use rustc_hir::def_id::DefId;

use std::{collections::HashMap, fmt::Display, io::Write, path::Path};

pub struct Statistics {
    pub api_count: usize,
    pub type_count: usize,
    pub generic_param_count: usize,
    pub edge_cnt: usize,
}

impl<'tcx> ApiDependencyGraph<'tcx> {
    pub fn new() -> ApiDependencyGraph<'tcx> {
        ApiDependencyGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
        }
    }

    pub fn inner_graph(&self) -> &InnerGraph<'tcx> {
        &self.graph
    }

    pub fn statistics(&self) -> Statistics {
        let mut api_cnt = 0;
        let mut ty_cnt = 0;
        let mut generic_param_cnt = 0;
        let mut edge_cnt = 0;

        for node in self.graph.node_indices() {
            match self.graph[node] {
                Node::Api(_) => api_cnt += 1,
                Node::Ty(_) => ty_cnt += 1,
                Node::GenericParamDef(..) => generic_param_cnt += 1,
            }
        }

        for _edge in self.graph.edge_indices() {
            edge_cnt += 1;
        }

        Statistics {
            api_count: api_cnt,
            type_count: ty_cnt,
            generic_param_count: generic_param_cnt,
            edge_cnt,
        }
    }

    pub fn get_node(&mut self, node: Node<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node.clone());
            self.node_indices.insert(node, node_index);
            node_index
        }
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex, edge: Edge) {
        self.graph.add_edge(src, dst, edge);
    }

    pub fn add_edge_once(&mut self, src: NodeIndex, dst: NodeIndex, edge: Edge) {
        if !self.graph.contains_edge(src, dst) {
            self.graph.add_edge(src, dst, edge);
        }
    }

    pub fn dump_to_dot<P: AsRef<Path>>(&self, path: P, tcx: TyCtxt<'tcx>) {
        let get_edge_attr =
            |_graph: &Graph<Node<'tcx>, Edge>, edge_ref: petgraph::graph::EdgeReference<Edge>| {
                let color = match edge_ref.weight() {
                    Edge::Arg(_) | Edge::Ret => "black",
                    Edge::Fn2Generic => "grey",
                };
                format!("label=\"{}\", color = {}", edge_ref.weight(), color)
            };
        let get_node_attr = |_graph: &Graph<Node<'tcx>, Edge>,
                             node_ref: (NodeIndex, &Node<'tcx>)| {
            format!("label={:?}, ", desc_str(node_ref.1.clone(), tcx))
                + match node_ref.1 {
                    Node::Api(_) => "color = blue",
                    Node::Ty(_) => "color = red",
                    Node::GenericParamDef(..) => "color = green",
                }
                + ", shape=box"
        };

        let dot = Dot::with_attr_getters(
            &self.graph,
            &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );
        let mut file = rap_create_file(path, "can not create dot file");
        write!(&mut file, "{:?}", dot).expect("fail when writing data to dot file");
        // println!("{:?}", dot);
    }
}

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Edge::Arg(no) => write!(f, "{}", no),
            Edge::Ret => write!(f, "r"),
            Edge::Fn2Generic => write!(f, ""),
        }
    }
}

impl Edge {
    pub fn arg(no: usize) -> Edge {
        Edge::Arg(no)
    }
    pub fn ret() -> Edge {
        Edge::Ret
    }
    pub fn fn2generic() -> Edge {
        Edge::Fn2Generic
    }
}

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
enum IntrinsicKind {
    Borrow,
}

pub fn desc_str<'tcx>(node: Node<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    match node {
        Node::Api(def_id) => tcx.def_path_str(def_id),
        Node::Ty(ty) => ty.desc_str(tcx),
        Node::GenericParamDef(_idx, index, sym, _is_lifetime) => {
            format!("{sym}/#{index}")
        }
    }
}

impl<'tcx> Node<'tcx> {
    pub fn api(id: impl IntoQueryParam<DefId>) -> Node<'tcx> {
        Node::Api(id.into_query_param())
    }
    pub fn ty(ty: Ty<'tcx>) -> Node<'tcx> {
        Node::Ty(TyWrapper::from(ty))
    }
    pub fn generic_param_def(
        fn_def_id: DefId,
        index: usize,
        name: impl ToString,
        is_lifetime: bool,
    ) -> Node<'tcx> {
        Node::GenericParamDef(fn_def_id, index, name.to_string(), is_lifetime)
    }
}
