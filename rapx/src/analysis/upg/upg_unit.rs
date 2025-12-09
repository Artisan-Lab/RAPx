use crate::analysis::utils::fn_info::*;
use petgraph::{
    Graph,
    dot::{Config, Dot},
    graph::{DiGraph, EdgeReference, NodeIndex},
};
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{mir::Local, ty::TyCtxt};
use std::{
    collections::HashSet,
    fmt::{self, Write},
    hash::Hash,
};

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

#[derive(Debug, Clone)]
pub struct UPGUnit {
    pub caller: FnInfo,
    pub callees: HashSet<FnInfo>,
    pub raw_ptrs: HashSet<Local>,
    pub static_muts: HashSet<DefId>,
    pub caller_cons: HashSet<FnInfo>,
    pub mut_methods: Vec<DefId>,
}

impl UPGUnit {
    pub fn new(
        caller: FnInfo,
        callees: HashSet<FnInfo>,
        raw_ptrs: HashSet<Local>,
        static_muts: HashSet<DefId>,
        caller_cons: HashSet<FnInfo>,
        mut_methods: Vec<DefId>,
    ) -> Self {
        Self {
            caller,
            callees,
            raw_ptrs,
            static_muts,
            caller_cons,
            mut_methods,
        }
    }

    pub fn count_basic_units(&self, data: &mut [u32]) {
        if self.caller.fn_safety == Safety::Unsafe && self.callees.is_empty() {
            data[0] += 1;
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[2] += 1;
                } else {
                    data[1] += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind != FnKind::Method {
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[4] += 1;
                } else {
                    data[3] += 1;
                }
            }
        }
        if self.caller.fn_safety == Safety::Unsafe && self.caller.fn_kind == FnKind::Method {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.fn_safety == Safety::Unsafe {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[7] += safe_cons;
                    data[8] += unsafe_cons;
                } else {
                    data[5] += safe_cons;
                    data[6] += unsafe_cons;
                }
            }
        }
        if self.caller.fn_safety == Safety::Safe && self.caller.fn_kind == FnKind::Method {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.fn_safety == Safety::Unsafe {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for callee in &self.callees {
                if callee.fn_kind == FnKind::Method {
                    data[11] += safe_cons;
                    data[12] += unsafe_cons;
                } else {
                    data[9] += safe_cons;
                    data[10] += unsafe_cons;
                }
            }
        }
    }

    pub fn get_node_ty(node: FnInfo) -> UPGNode {
        match node.fn_safety {
            Safety::Unsafe => match node.fn_kind {
                FnKind::Constructor => UPGNode::UnsafeFn(node.def_id, "septagon".to_string()),
                FnKind::Method => UPGNode::UnsafeFn(node.def_id, "ellipse".to_string()),
                FnKind::Fn => UPGNode::UnsafeFn(node.def_id, "box".to_string()),
                FnKind::Intrinsic => UPGNode::UnsafeFn(node.def_id, "box".to_string()),
            },
            Safety::Safe => match node.fn_kind {
                FnKind::Constructor => UPGNode::SafeFn(node.def_id, "septagon".to_string()),
                FnKind::Method => UPGNode::SafeFn(node.def_id, "ellipse".to_string()),
                FnKind::Fn => UPGNode::SafeFn(node.def_id, "box".to_string()),
                FnKind::Intrinsic => UPGNode::SafeFn(node.def_id, "box".to_string()),
            },
        }
    }

    pub fn generate_dot_str(&self) -> String {
        let mut graph: Graph<UPGNode, UPGEdge> = DiGraph::new();
        let get_edge_attr = |_graph: &Graph<UPGNode, UPGEdge>,
                             edge_ref: EdgeReference<'_, UPGEdge>| {
            match edge_ref.weight() {
                UPGEdge::CallerToCallee => "color=black, style=solid",
                UPGEdge::ConsToMethod => "color=black, style=dotted",
                UPGEdge::MutToCaller => "color=blue, style=dashed",
            }
            .to_owned()
        };
        let get_node_attr =
            |_graph: &Graph<UPGNode, UPGEdge>, node_ref: (NodeIndex, &UPGNode)| match node_ref.1 {
                UPGNode::SafeFn(def_id, shape) => {
                    format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
                }
                UPGNode::UnsafeFn(def_id, shape) => {
                    let label = format!("{:?}\n ", def_id);
                    let node_attr = format!("label={:?}, shape={:?}, color=red", label, shape);
                    node_attr
                }
                UPGNode::MergedCallerCons(label) => {
                    format!(
                        "label=\"{}\", shape=box, style=filled, fillcolor=lightgrey",
                        label
                    )
                }
                UPGNode::MutMethods(label) => {
                    format!(
                        "label=\"{}\", shape=octagon, style=filled, fillcolor=lightyellow",
                        label
                    )
                }
            };

        let caller_node = graph.add_node(Self::get_node_ty(self.caller));
        if !self.caller_cons.is_empty() {
            let cons_labels: Vec<String> = self
                .caller_cons
                .iter()
                .map(|con| format!("{:?}", con.def_id))
                .collect();
            let merged_label = format!("Caller Constructors\n{}", cons_labels.join("\n"));
            let merged_cons_node = graph.add_node(UPGNode::MergedCallerCons(merged_label));
            graph.add_edge(merged_cons_node, caller_node, UPGEdge::ConsToMethod);
        }

        if !self.mut_methods.is_empty() {
            let mut_method_labels: Vec<String> = self
                .mut_methods
                .iter()
                .map(|def_id| format!("{:?}", def_id))
                .collect();
            let merged_label = format!("Mutable Methods\n{}", mut_method_labels.join("\n"));

            let mut_methods_node = graph.add_node(UPGNode::MutMethods(merged_label));
            graph.add_edge(mut_methods_node, caller_node, UPGEdge::MutToCaller);
        }

        /*
        for (callee, cons) in &self.callee_cons_pair {
            let callee_node = graph.add_node(Self::get_node_ty(*callee));
            for callee_cons in cons {
                let callee_cons_node = graph.add_node(Self::get_node_ty(*callee_cons));
                graph.add_edge(callee_cons_node, callee_node, UPGEdge::ConsToMethod);
            }
            graph.add_edge(caller_node, callee_node, UPGEdge::CallerToCallee);
        }
        */
        let mut dot_str = String::new();
        let dot = Dot::with_attr_getters(
            &graph,
            // &[Config::NodeNoLabel, Config::EdgeNoLabel],
            &[Config::NodeNoLabel],
            &get_edge_attr,
            &get_node_attr,
        );

        write!(dot_str, "{}", dot).unwrap();
        // println!("{}", dot_str);
        dot_str
    }

    pub fn print_self(&self, tcx: TyCtxt<'_>) {
        let caller_sp = get_sp(tcx, self.caller.def_id);
        let caller_label: Vec<_> = caller_sp.clone().into_iter().collect();

        let mut combined_callee_sp = HashSet::new();
        let combined_labels: Vec<_> = combined_callee_sp.clone().into_iter().collect();
        println!(
            "Caller: {:?}.\n--Caller's constructors: {:?}.\n--SP labels: {:?}.",
            get_cleaned_def_path_name(tcx, self.caller.def_id),
            self.caller_cons
                .iter()
                .filter(|cons| cons.fn_safety == Safety::Unsafe)
                .map(|node_type| get_cleaned_def_path_name(tcx, node_type.def_id))
                .collect::<Vec<_>>(),
            caller_label
        );
        for callee in &self.callees {
            let callee_sp = get_sp(tcx, callee.def_id);
            combined_callee_sp.extend(callee_sp); // Merge sp of each callee
        }
        println!(
            "Callee: {:?}.\n--Combined Callee Labels: {:?}",
            self.callees
                .iter()
                .map(|callee| get_cleaned_def_path_name(tcx, callee.def_id))
                .collect::<Vec<_>>(),
            combined_labels
        );
    }
}
