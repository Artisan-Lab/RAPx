use std::{
    collections::{HashMap, HashSet},
    fmt::{self, Write},
};

use crate::analysis::{upg::UPGUnit, utils::fn_info::*};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum UPGNode {
    SafeFn(DefId, String),
    UnsafeFn(DefId, String),
    MergedCallerCons(String),
    MutMethods(String),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum UPGEdge {
    CallerToCallee,
    ConsToMethod,
    MutToCaller,
}

impl fmt::Display for UPGNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UPGNode::SafeFn(_, _) => write!(f, "Safe"),
            UPGNode::UnsafeFn(_, _) => write!(f, "Unsafe"),
            UPGNode::MergedCallerCons(_) => write!(f, "MergedCallerCons"),
            UPGNode::MutMethods(_) => write!(f, "MutMethods"),
        }
    }
}

impl fmt::Display for UPGEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UPGEdge::CallerToCallee => write!(f, "CallerToCallee"),
            UPGEdge::ConsToMethod => write!(f, "ConsToMethod"),
            UPGEdge::MutToCaller => write!(f, "MutToCaller"),
        }
    }
}

/// Holds graph data for a single module before DOT generation.
pub struct UPGraph {
    // Nodes grouped by their associated struct/type name.
    structs: HashMap<String, HashSet<FnInfo>>,
    // Edges between DefIds with their type.
    edges: HashSet<(DefId, DefId, UPGEdge)>,
    // Pre-generated DOT attribute strings for each node (DefId).
    nodes: HashMap<DefId, String>,
}

impl UPGraph {
    pub fn new() -> Self {
        Self {
            structs: HashMap::new(),
            edges: HashSet::new(),
            nodes: HashMap::new(),
        }
    }

    pub fn add_node(&mut self, tcx: TyCtxt<'_>, node: FnInfo, custom_label: Option<String>) {
        let adt_name = self.get_adt_name(tcx, node.def_id);
        self.structs.entry(adt_name).or_default().insert(node);

        if !self.nodes.contains_key(&node.def_id) || custom_label.is_some() {
            let attr = if let Some(label) = custom_label {
                if node.fn_kind == FnKind::Constructor {
                    format!(
                        "label=\"{}\", shape=\"septagon\", style=\"filled\", fillcolor=\"#f0f0f0\", color=\"#555555\"",
                        label
                    )
                } else {
                    format!(
                        "label=\"{}\", shape=\"ellipse\", style=\"filled\", fillcolor=\"#f0f0f0\", color=\"#555555\"",
                        label
                    )
                }
            } else {
                let upg_node = UPGUnit::get_node_ty(node);
                self.node_to_dot_attr(tcx, &upg_node)
            };

            self.nodes.insert(node.def_id, attr);
        }
    }

    pub fn add_edge(&mut self, from: DefId, to: DefId, edge_type: UPGEdge) {
        if from == to {
            return;
        }
        self.edges.insert((from, to, edge_type));
    }

    pub fn get_adt_name(&self, tcx: TyCtxt<'_>, def_id: DefId) -> String {
        match tcx.def_kind(def_id) {
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                let raw_name = tcx.type_of(def_id).skip_binder().to_string();
                return raw_name
                    .split('<')
                    .next()
                    .unwrap_or(&raw_name)
                    .trim()
                    .to_string();
            }
            _ => {}
        }
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                let ty = tcx.type_of(impl_id).skip_binder();
                let raw_name = ty.to_string();
                return raw_name
                    .split('<')
                    .next()
                    .unwrap_or(&raw_name)
                    .trim()
                    .to_string();
            }
        }
        "Free_Functions".to_string()
    }

    fn node_to_dot_attr(&self, _tcx: TyCtxt<'_>, node: &UPGNode) -> String {
        match node {
            UPGNode::SafeFn(def_id, shape) => {
                format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
            }
            UPGNode::UnsafeFn(def_id, shape) => {
                let label = format!("{:?}", def_id);
                format!("label=\"{}\", shape={:?}, color=red", label, shape)
            }
            _ => "label=\"Unknown\"".to_string(),
        }
    }

    pub fn upg_unit_string(&self, module_name: &str) -> String {
        let mut dot = String::new();
        let graph_id = module_name
            .replace("::", "_")
            .replace(|c: char| !c.is_alphanumeric(), "_");

        writeln!(dot, "digraph {} {{", graph_id).unwrap();
        writeln!(dot, "    compound=true;").unwrap();
        writeln!(dot, "    rankdir=LR;").unwrap();

        for (struct_name, nodes) in &self.structs {
            let cluster_id = format!(
                "cluster_{}",
                struct_name.replace(|c: char| !c.is_alphanumeric(), "_")
            );

            writeln!(dot, "    subgraph {} {{", cluster_id).unwrap();
            writeln!(dot, "        label=\"{}\";", struct_name).unwrap();
            writeln!(dot, "        style=dashed;").unwrap();
            writeln!(dot, "        color=gray;").unwrap();

            for node in nodes {
                let def_id = node.def_id;
                let node_id =
                    format!("n_{:?}", def_id).replace(|c: char| !c.is_alphanumeric(), "_");

                if let Some(attr) = self.nodes.get(&def_id) {
                    writeln!(dot, "        {} [{}];", node_id, attr).unwrap();
                }
            }
            writeln!(dot, "    }}").unwrap();
        }

        for (from, to, edge_type) in &self.edges {
            let from_id = format!("n_{:?}", from).replace(|c: char| !c.is_alphanumeric(), "_");
            let to_id = format!("n_{:?}", to).replace(|c: char| !c.is_alphanumeric(), "_");

            let attr = match edge_type {
                UPGEdge::CallerToCallee => "color=black, style=solid",
                UPGEdge::ConsToMethod => "color=black, style=dotted",
                UPGEdge::MutToCaller => "color=blue, style=dashed",
            };

            writeln!(dot, "    {} -> {} [{}];", from_id, to_id, attr).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }
}
