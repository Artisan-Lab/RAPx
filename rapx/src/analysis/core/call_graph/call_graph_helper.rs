use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use std::collections::HashSet;
use std::{collections::HashMap, hash::Hash};

use crate::rap_info;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Node {
    def_id: DefId,
    def_path: String,
}

impl Node {
    pub fn new(def_id: DefId, def_path: &String) -> Self {
        Self {
            def_id: def_id,
            def_path: def_path.clone(),
        }
    }

    pub fn get_def_id(&self) -> DefId {
        self.def_id
    }

    pub fn get_def_path(&self) -> String {
        self.def_path.clone()
    }
}

pub struct CallGraphInfo<'tcx> {
    pub functions: HashMap<usize, Node>, // id -> node
    pub function_calls: HashMap<usize, Vec<(usize, &'tcx mir::Terminator<'tcx>)>>, // caller_id -> Vec<(callee_id, terminator)>
    pub node_registry: HashMap<String, usize>,                                     // path -> id
}

impl<'tcx> CallGraphInfo<'tcx> {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),
            function_calls: HashMap::new(),
            node_registry: HashMap::new(),
        }
    }

    pub fn get_node_num(&self) -> usize {
        self.functions.len()
    }

    pub fn get_callees_path(&self, caller_def_path: &String) -> Option<HashSet<String>> {
        let mut callees_path: HashSet<String> = HashSet::new();
        if let Some(caller_id) = self.node_registry.get(caller_def_path) {
            if let Some(callees) = self.function_calls.get(caller_id) {
                for (id, _terminator) in callees {
                    if let Some(callee_node) = self.functions.get(id) {
                        callees_path.insert(callee_node.get_def_path());
                    }
                }
            }
            Some(callees_path)
        } else {
            None
        }
    }

    pub fn add_node(&mut self, def_id: DefId, def_path: &String) {
        if self.node_registry.get(def_path).is_none() {
            let id = self.node_registry.len();
            let node = Node::new(def_id, def_path);
            self.node_registry.insert(def_path.clone(), id);
            self.functions.insert(id, node);
        }
    }

    pub fn add_funciton_call_edge(
        &mut self,
        caller_id: usize,
        callee_id: usize,
        terminator_stmt: &'tcx mir::Terminator<'tcx>,
    ) {
        let entry = self
            .function_calls
            .entry(caller_id)
            .or_insert_with(Vec::new);
        entry.push((callee_id, terminator_stmt));
    }

    pub fn get_noed_by_path(&self, def_path: &String) -> Option<usize> {
        self.node_registry.get(def_path).copied()
    }
    pub fn get_callers_map(&self) -> HashMap<usize, Vec<(usize, &'tcx mir::Terminator<'tcx>)>> {
        let mut callers_map: HashMap<usize, Vec<(usize, &'tcx mir::Terminator<'tcx>)>> =
            HashMap::new();

        for (&caller_id, calls_vec) in &self.function_calls {
            for (callee_id, terminator) in calls_vec {
                callers_map
                    .entry(*callee_id)
                    .or_insert_with(Vec::new)
                    .push((caller_id, *terminator));
            }
        }

        callers_map
    }
    pub fn print_call_graph(&self) {
        rap_info!("CallGraph Analysis:");
        for (caller_id, callees) in &self.function_calls {
            if let Some(caller_node) = self.functions.get(caller_id) {
                for (callee_id, terminator_stmt) in callees {
                    if let Some(callee_node) = self.functions.get(callee_id) {
                        let caller_def_path = caller_node.get_def_path();
                        let callee_def_path = callee_node.get_def_path();
                        rap_info!(
                            "{}:{} -> {}:{} @ {:?}",
                            caller_id,
                            caller_def_path,
                            *callee_id,
                            callee_def_path,
                            terminator_stmt.kind
                        );
                    }
                }
            }
        }
    }
    pub fn get_reverse_post_order(&self) -> Vec<DefId> {
        let mut visited = HashSet::new();
        let mut post_order_ids = Vec::new(); // Will store the post-order traversal of `usize` IDs

        // Iterate over all functions defined in the graph to handle disconnected components
        for &node_id in self.functions.keys() {
            if !visited.contains(&node_id) {
                self.dfs_post_order(node_id, &mut visited, &mut post_order_ids);
            }
        }

        // Map the ordered `usize` IDs back to `DefId`s for the analysis pipeline
        let mut analysis_order: Vec<DefId> = post_order_ids
            .into_iter()
            .map(|id| {
                self.functions
                    .get(&id)
                    .expect("Node ID must exist in functions map")
                    .def_id
            })
            .collect();

        // Reversing the post-order gives a topological sort (bottom-up)
        analysis_order.reverse();

        analysis_order
    }

    /// Helper function to perform a recursive depth-first search.
    fn dfs_post_order(
        &self,
        node_id: usize,
        visited: &mut HashSet<usize>,
        post_order_ids: &mut Vec<usize>,
    ) {
        // Mark the current node as visited
        visited.insert(node_id);

        // Visit all callees (children) of the current node
        if let Some(callees) = self.function_calls.get(&node_id) {
            for (callee_id, _terminator) in callees {
                if !visited.contains(callee_id) {
                    self.dfs_post_order(*callee_id, visited, post_order_ids);
                }
            }
        }

        // After visiting all children, add the current node to the post-order list
        post_order_ids.push(node_id);
    }
}
