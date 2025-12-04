use crate::analysis::utils::fn_info::*;
use petgraph::Graph;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{DiGraph, EdgeReference, NodeIndex};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::collections::HashSet;
use std::fmt::{self, Write};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum UigNode {
    Safe(DefId, String),
    Unsafe(DefId, String),
    MergedCallerCons(String),
    MutMethods(String),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum UigEdge {
    CallerToCallee,
    ConsToMethod,
    MutToCaller,
}

impl fmt::Display for UigNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UigNode::Safe(_, _) => write!(f, "Safe"),
            UigNode::Unsafe(_, _) => write!(f, "Unsafe"),
            UigNode::MergedCallerCons(_) => write!(f, "MergedCallerCons"),
            UigNode::MutMethods(_) => write!(f, "MutMethods"),
        }
    }
}

impl fmt::Display for UigEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UigEdge::CallerToCallee => write!(f, "CallerToCallee"),
            UigEdge::ConsToMethod => write!(f, "ConsToMethod"),
            UigEdge::MutToCaller => write!(f, "MutToCaller"),
        }
    }
}

// def_id, is_unsafe_function(true, false), function type(0-constructor, 1-method, 2-function)
pub type NodeType = (DefId, bool, usize);

#[derive(Debug, Clone)]
pub struct UigUnit {
    pub caller: NodeType,
    pub caller_cons: Vec<NodeType>,
    pub callee_cons_pair: HashSet<(NodeType, Vec<NodeType>)>,
    pub mut_methods: Vec<DefId>,
}

impl UigUnit {
    pub fn new(caller: NodeType, caller_cons: Vec<NodeType>) -> Self {
        Self {
            caller,
            caller_cons,
            callee_cons_pair: HashSet::default(),
            mut_methods: Vec::new(),
        }
    }

    pub fn new_by_pair(
        caller: NodeType,
        caller_cons: Vec<NodeType>,
        callee_cons_pair: HashSet<(NodeType, Vec<NodeType>)>,
        mut_methods: Vec<DefId>,
    ) -> Self {
        Self {
            caller,
            caller_cons,
            callee_cons_pair,
            mut_methods,
        }
    }

    pub fn count_basic_units(&self, data: &mut [u32]) {
        if self.caller.1 && self.callee_cons_pair.is_empty() {
            data[0] += 1;
        }
        if !self.caller.1 && self.caller.2 != 1 {
            for (callee, _) in &self.callee_cons_pair {
                if callee.2 == 1 {
                    data[2] += 1;
                } else {
                    data[1] += 1;
                }
            }
        }
        if self.caller.1 && self.caller.2 != 1 {
            for (callee, _) in &self.callee_cons_pair {
                if callee.2 == 1 {
                    data[4] += 1;
                } else {
                    data[3] += 1;
                }
            }
        }
        if self.caller.1 && self.caller.2 == 1 {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.1 {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for (callee, _) in &self.callee_cons_pair {
                if callee.2 == 1 {
                    data[7] += safe_cons;
                    data[8] += unsafe_cons;
                } else {
                    data[5] += safe_cons;
                    data[6] += unsafe_cons;
                }
            }
        }
        if !self.caller.1 && self.caller.2 == 1 {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.1 {
                    unsafe_cons += 1;
                } else {
                    safe_cons += 1;
                }
            }
            if unsafe_cons == 0 && safe_cons == 0 {
                safe_cons = 1;
            }
            for (callee, _) in &self.callee_cons_pair {
                if callee.2 == 1 {
                    data[11] += safe_cons;
                    data[12] += unsafe_cons;
                } else {
                    data[9] += safe_cons;
                    data[10] += unsafe_cons;
                }
            }
        }
    }

    /// (node.0, node.1, node.2) : (def_id, is_unsafe, type_of_func--0:cons,1:method,2:function)
    pub fn get_node_ty(node: NodeType) -> UigNode {
        match (node.1, node.2) {
            (true, 0) => UigNode::Unsafe(node.0, "septagon".to_string()),
            (true, 1) => UigNode::Unsafe(node.0, "ellipse".to_string()),
            (true, 2) => UigNode::Unsafe(node.0, "box".to_string()),
            (false, 0) => UigNode::Safe(node.0, "septagon".to_string()),
            (false, 1) => UigNode::Safe(node.0, "ellipse".to_string()),
            (false, 2) => UigNode::Safe(node.0, "box".to_string()),
            _ => UigNode::Safe(node.0, "ellipse".to_string()),
        }
    }

    pub fn generate_dot_str(&self) -> String {
        let mut graph: Graph<UigNode, UigEdge> = DiGraph::new();
        let get_edge_attr = |_graph: &Graph<UigNode, UigEdge>,
                             edge_ref: EdgeReference<'_, UigEdge>| {
            match edge_ref.weight() {
                UigEdge::CallerToCallee => "color=black, style=solid",
                UigEdge::ConsToMethod => "color=black, style=dotted",
                UigEdge::MutToCaller => "color=blue, style=dashed",
            }
            .to_owned()
        };
        let get_node_attr =
            |_graph: &Graph<UigNode, UigEdge>, node_ref: (NodeIndex, &UigNode)| match node_ref.1 {
                UigNode::Safe(def_id, shape) => {
                    format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
                }
                UigNode::Unsafe(def_id, shape) => {
                    let label = format!("{:?}\n ", def_id);
                    let node_attr = format!("label={:?}, shape={:?}, color=red", label, shape);
                    node_attr
                }
                UigNode::MergedCallerCons(label) => {
                    format!(
                        "label=\"{}\", shape=box, style=filled, fillcolor=lightgrey",
                        label
                    )
                }
                UigNode::MutMethods(label) => {
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
                .map(|(def_id, _, _)| format!("{:?}", def_id))
                .collect();
            let merged_label = format!("Caller Constructors\n{}", cons_labels.join("\n"));
            let merged_cons_node = graph.add_node(UigNode::MergedCallerCons(merged_label));
            graph.add_edge(merged_cons_node, caller_node, UigEdge::ConsToMethod);
        }

        if !self.mut_methods.is_empty() {
            let mut_method_labels: Vec<String> = self
                .mut_methods
                .iter()
                .map(|def_id| format!("{:?}", def_id))
                .collect();
            let merged_label = format!("Mutable Methods\n{}", mut_method_labels.join("\n"));

            let mut_methods_node = graph.add_node(UigNode::MutMethods(merged_label));
            graph.add_edge(mut_methods_node, caller_node, UigEdge::MutToCaller);
        }

        for (callee, cons) in &self.callee_cons_pair {
            let callee_node = graph.add_node(Self::get_node_ty(*callee));
            for callee_cons in cons {
                let callee_cons_node = graph.add_node(Self::get_node_ty(*callee_cons));
                graph.add_edge(callee_cons_node, callee_node, UigEdge::ConsToMethod);
            }
            graph.add_edge(caller_node, callee_node, UigEdge::CallerToCallee);
        }

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
        let caller_sp = get_sp(tcx, self.caller.0);
        let caller_label: Vec<_> = caller_sp.clone().into_iter().collect();

        let mut combined_callee_sp = HashSet::new();
        for (callee, _sp_vec) in &self.callee_cons_pair {
            let callee_sp = get_sp(tcx, callee.0);
            combined_callee_sp.extend(callee_sp); // Merge sp of each callee
        }
        let combined_labels: Vec<_> = combined_callee_sp.clone().into_iter().collect();
        println!(
            "Caller: {:?}.\n--Caller's constructors: {:?}.\n--SP labels: {:?}.",
            get_cleaned_def_path_name(tcx, self.caller.0),
            self.caller_cons
                .iter()
                .filter(|cons| cons.1)
                .map(|node_type| get_cleaned_def_path_name(tcx, node_type.0))
                .collect::<Vec<_>>(),
            caller_label
        );
        println!(
            "Callee: {:?}.\n--Combined Callee Labels: {:?}",
            self.callee_cons_pair
                .iter()
                .map(|(node_type, _)| get_cleaned_def_path_name(tcx, node_type.0))
                .collect::<Vec<_>>(),
            combined_labels
        );
    }
}
