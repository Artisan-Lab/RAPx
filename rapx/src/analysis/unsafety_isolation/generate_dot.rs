use crate::analysis::unsafety_isolation::UnsafetyIsolationCheck;
use crate::analysis::utils::fn_info::*;
use petgraph::dot::{Config, Dot};
use petgraph::graph::{DiGraph, EdgeReference, NodeIndex};
use petgraph::Graph;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::collections::HashSet;
use std::fmt::{self, Write};

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum UigNode {
    Safe(DefId, String),
    Unsafe(DefId, String),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum UigEdge {
    CallerToCallee,
    ConsToMethod,
}

impl fmt::Display for UigNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UigNode::Safe(_, _) => write!(f, "Safe"),
            UigNode::Unsafe(_, _) => write!(f, "Unsafe"),
        }
    }
}

impl fmt::Display for UigEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UigEdge::CallerToCallee => write!(f, "CallerToCallee"),
            UigEdge::ConsToMethod => write!(f, "ConsToMethod"),
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
}

impl UigUnit {
    pub fn new(caller: NodeType, caller_cons: Vec<NodeType>) -> Self {
        Self {
            caller,
            caller_cons,
            callee_cons_pair: HashSet::default(),
        }
    }

    pub fn new_by_pair(
        caller: NodeType,
        caller_cons: Vec<NodeType>,
        callee_cons_pair: HashSet<(NodeType, Vec<NodeType>)>,
    ) -> Self {
        Self {
            caller,
            caller_cons,
            callee_cons_pair,
        }
    }

    pub fn count_basic_units(&self, data: &mut [u32]) {
        if self.caller.1 == true && self.callee_cons_pair.len() == 0 {
            data[0] += 1;
        }
        if self.caller.1 == false && self.caller.2 != 1 {
            for (callee, _) in &self.callee_cons_pair {
                if callee.2 == 1 {
                    data[2] += 1;
                } else {
                    data[1] += 1;
                }
            }
        }
        if self.caller.1 == true && self.caller.2 != 1 {
            for (callee, _) in &self.callee_cons_pair {
                if callee.2 == 1 {
                    data[4] += 1;
                } else {
                    data[3] += 1;
                }
            }
        }
        if self.caller.1 == true && self.caller.2 == 1 {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.1 == true {
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
                    data[7] += 1 * safe_cons;
                    data[8] += 1 * unsafe_cons;
                } else {
                    data[5] += 1 * safe_cons;
                    data[6] += 1 * unsafe_cons;
                }
            }
        }
        if self.caller.1 == false && self.caller.2 == 1 {
            let mut unsafe_cons = 0;
            let mut safe_cons = 0;
            for cons in &self.caller_cons {
                if cons.1 == true {
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
                    data[11] += 1 * safe_cons;
                    data[12] += 1 * unsafe_cons;
                } else {
                    data[9] += 1 * safe_cons;
                    data[10] += 1 * unsafe_cons;
                }
            }
        }
    }

    pub fn get_node_ty(node: NodeType) -> UigNode {
        match (node.1, node.2) {
            (true, 0) => UigNode::Unsafe(node.0, "doublecircle".to_string()),
            (true, 1) => UigNode::Unsafe(node.0, "ellipse".to_string()),
            (true, 2) => UigNode::Unsafe(node.0, "box".to_string()),
            (false, 0) => UigNode::Safe(node.0, "doublecircle".to_string()),
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
            }
            .to_owned()
        };
        let get_node_attr = |_graph: &Graph<UigNode, UigEdge>, node_ref: (NodeIndex, &UigNode)| {
            match node_ref.1 {
                UigNode::Safe(def_id, shape) => {
                    format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
                }
                UigNode::Unsafe(def_id, shape) => {
                    // let sps = self.get_sp(*def_id);
                    // let mut label = format!("{:?}\n ", def_id);
                    // for sp_name in sps {
                    //     label.push_str(&format!(" {}", sp_name));
                    // }
                    let label = format!("{:?}\n ", def_id);
                    let node_attr = format!("label={:?}, shape={:?}, color=red", label, shape);
                    node_attr
                }
            }
        };

        let caller_node = graph.add_node(Self::get_node_ty(self.caller));
        for caller_cons in &self.caller_cons {
            let caller_cons_node = graph.add_node(Self::get_node_ty(*caller_cons));
            graph.add_edge(caller_cons_node, caller_node, UigEdge::ConsToMethod);
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
        // println!("{}",dot_str);
        dot_str
    }

    pub fn compare_labels(&self, tcx: TyCtxt<'_>) {
        let caller_sp = get_sp(tcx, self.caller.0);
        // for caller_con in &self.caller_cons {
        //     if caller_con.1 != true {
        //         // if constructor is safe, it won't have labels.
        //         continue;
        //     }
        //     let caller_con_sp = Self::get_sp(caller_con.0);
        //     caller_sp.extend(caller_con_sp); // Merge sp of each unsafe constructor
        // }
        let caller_label: Vec<_> = caller_sp.clone().into_iter().collect();

        let mut combined_callee_sp = HashSet::new();
        for (callee, _sp_vec) in &self.callee_cons_pair {
            let callee_sp = get_sp(tcx, callee.0);
            combined_callee_sp.extend(callee_sp); // Merge sp of each callee
        }
        let combined_labels: Vec<_> = combined_callee_sp.clone().into_iter().collect();

        if caller_sp == combined_callee_sp {
            // println!("----------same sp------------");
            // println!(
            //     "Caller: {:?}.\n--Caller's constructors: {:?}.\n--SP labels: {:?}.",
            //     Self::get_cleaned_def_path_name(self.caller.0),
            //     self.caller_cons
            //         .iter()
            //         .map(|node_type| Self::get_cleaned_def_path_name(node_type.0))
            //         .collect::<Vec<_>>(),
            //     caller_label
            // );
            // println!(
            //     "Callee: {:?}.\n--Combined Callee Labels: {:?}",
            //     self.callee_cons_pair
            //         .iter()
            //         .map(|(node_type, _)| Self::get_cleaned_def_path_name(node_type.0))
            //         .collect::<Vec<_>>(),
            //     combined_labels
            // );
        } else {
            println!("----------unmatched sp------------");
            println!(
                "Caller: {:?}.\n--Caller's constructors: {:?}.\n--SP labels: {:?}.",
                get_cleaned_def_path_name(tcx, self.caller.0),
                self.caller_cons
                    .iter()
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
                .filter(|cons| cons.1 == true)
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

#[derive(PartialEq)]
pub enum UigOp {
    DrawPic,
    TypeCount,
}

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    pub fn get_node_name_by_def_id(&self, def_id: DefId) -> String {
        if let Some(node) = self.nodes.iter().find(|n| n.node_id == def_id) {
            return node.node_name.clone();
        }
        String::new()
    }

    pub fn get_node_type_by_def_id(&self, def_id: DefId) -> usize {
        if let Some(node) = self.nodes.iter().find(|n| n.node_id == def_id) {
            return node.node_type;
        }
        2
    }

    pub fn get_node_unsafety_by_def_id(&self, def_id: DefId) -> bool {
        if let Some(node) = self.nodes.iter().find(|n| n.node_id == def_id) {
            return node.node_unsafety;
        }
        false
    }

    pub fn get_adjacent_nodes_by_def_id(&self, def_id: DefId) -> Vec<DefId> {
        let mut nodes = Vec::new();
        if let Some(node) = self.nodes.iter().find(|n| n.node_id == def_id) {
            nodes.extend(node.callees.clone());
            nodes.extend(node.methods.clone());
            nodes.extend(node.callers.clone());
            nodes.extend(node.constructors.clone());
        }
        nodes
    }

    pub fn get_constructor_nodes_by_def_id(&self, def_id: DefId) -> Vec<DefId> {
        let mut nodes = Vec::new();
        if let Some(node) = self.nodes.iter().find(|n| n.node_id == def_id) {
            nodes.extend(node.constructors.clone());
        }
        nodes
    }
}
