use std::collections::{HashMap, HashSet};
use std::fmt::Write;

use crate::analysis::unsafety_isolation::UnsafetyIsolationCheck;
use crate::analysis::unsafety_isolation::draw_dot::render_dot_graphs;
use crate::analysis::unsafety_isolation::generate_dot::{NodeType, UigEdge, UigNode, UigUnit};
use crate::analysis::utils::fn_info::{check_safety, get_type};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

impl<'tcx> UnsafetyIsolationCheck<'tcx> {
    /// Main function to aggregate data and render DOT graphs per module.
    pub fn render_module_dot(&self) {
        let mut modules_data: HashMap<String, ModuleGraphData> = HashMap::new();

        let mut collect_unit = |unit: &UigUnit| {
            let caller_id = unit.caller.0;
            let module_name = self.get_module_name(caller_id);

            let module_data = modules_data
                .entry(module_name)
                .or_insert_with(ModuleGraphData::new);

            module_data.add_node(self.tcx, unit.caller);

            // Edge from associated item (constructor) to the method.
            for cons in &unit.caller_cons {
                module_data.add_node(self.tcx, *cons);
                module_data.add_edge(cons.0, unit.caller.0, UigEdge::ConsToMethod);
            }

            // Edge for mutable access to the caller.
            for mut_method_id in &unit.mut_methods {
                let node_type = get_type(self.tcx, *mut_method_id);
                let is_unsafe = check_safety(self.tcx, *mut_method_id);
                let node = (*mut_method_id, is_unsafe, node_type);

                module_data.add_node(self.tcx, node);
                module_data.add_edge(*mut_method_id, unit.caller.0, UigEdge::MutToCaller);
            }

            // Edge representing a call from caller to callee.
            for (callee, callee_cons_vec) in &unit.callee_cons_pair {
                module_data.add_node(self.tcx, *callee);
                module_data.add_edge(unit.caller.0, callee.0, UigEdge::CallerToCallee);

                for callee_cons in callee_cons_vec {
                    module_data.add_node(self.tcx, *callee_cons);
                    module_data.add_edge(callee_cons.0, callee.0, UigEdge::ConsToMethod);
                }
            }
        };

        // Aggregate all Units
        for uig in &self.uigs {
            collect_unit(uig);
        }
        for uig in &self.single {
            collect_unit(uig);
        }

        // Generate string of dot
        let mut final_dots = Vec::new();
        for (mod_name, data) in modules_data {
            let dot = data.generate_dot_string(&mod_name);
            final_dots.push((mod_name, dot));
        }

        render_dot_graphs(final_dots);
    }

    /// get module of DefId
    fn get_module_name(&self, def_id: DefId) -> String {
        let tcx = self.tcx;
        let parent_mod = tcx.parent_module_from_def_id(def_id.expect_local());
        let mod_def_id = parent_mod.to_def_id();

        let path = tcx.def_path_str(mod_def_id);
        if path.is_empty() {
            "root_module".to_string()
        } else {
            path
        }
    }
}

/// Holds graph data for a single module before DOT generation.
struct ModuleGraphData {
    // Nodes grouped by their associated struct/type name.
    struct_clusters: HashMap<String, HashSet<NodeType>>,
    // Edges between DefIds with their type.
    edges: HashSet<(DefId, DefId, UigEdge)>,
    // Pre-generated DOT attribute strings for each node (DefId).
    node_styles: HashMap<DefId, String>,
}

impl ModuleGraphData {
    fn new() -> Self {
        Self {
            struct_clusters: HashMap::new(),
            edges: HashSet::new(),
            node_styles: HashMap::new(),
        }
    }

    fn add_node(&mut self, tcx: TyCtxt<'_>, node: NodeType) {
        let (def_id, _, _) = node;
        let struct_name = self.get_struct_group_name(tcx, def_id);
        self.struct_clusters
            .entry(struct_name)
            .or_default()
            .insert(node);

        if !self.node_styles.contains_key(&def_id) {
            let uig_node = UigUnit::get_node_ty(node);
            let attr = self.node_to_dot_attr(tcx, &uig_node);
            self.node_styles.insert(def_id, attr);
        }
    }

    fn add_edge(&mut self, from: DefId, to: DefId, edge_type: UigEdge) {
        if from == to {
            return;
        }
        self.edges.insert((from, to, edge_type));
    }

    fn get_struct_group_name(&self, tcx: TyCtxt<'_>, def_id: DefId) -> String {
        if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                let ty = tcx.type_of(impl_id).skip_binder();
                let raw_name = ty.to_string();
                let clean_name = raw_name
                    .split('<')
                    .next()
                    .unwrap_or(&raw_name)
                    .trim()
                    .to_string();
                return clean_name;
            }
        }
        "Free_Functions".to_string()
    }

    fn node_to_dot_attr(&self, _tcx: TyCtxt<'_>, node: &UigNode) -> String {
        match node {
            UigNode::Safe(def_id, shape) => {
                format!("label=\"{:?}\", color=black, shape={:?}", def_id, shape)
            }
            UigNode::Unsafe(def_id, shape) => {
                let label = format!("{:?}", def_id);
                format!("label=\"{}\", shape={:?}, color=red", label, shape)
            }
            _ => "label=\"Unknown\"".to_string(),
        }
    }

    fn generate_dot_string(&self, module_name: &str) -> String {
        let mut dot = String::new();
        let graph_id = module_name
            .replace("::", "_")
            .replace(|c: char| !c.is_alphanumeric(), "_");

        writeln!(dot, "digraph {} {{", graph_id).unwrap();
        writeln!(dot, "    compound=true;").unwrap();
        writeln!(dot, "    rankdir=LR;").unwrap();

        for (struct_name, nodes) in &self.struct_clusters {
            let cluster_id = format!(
                "cluster_{}",
                struct_name.replace(|c: char| !c.is_alphanumeric(), "_")
            );

            writeln!(dot, "    subgraph {} {{", cluster_id).unwrap();
            writeln!(dot, "        label=\"{}\";", struct_name).unwrap();
            writeln!(dot, "        style=dashed;").unwrap();
            writeln!(dot, "        color=gray;").unwrap();

            for node in nodes {
                let def_id = node.0;
                let node_id =
                    format!("n_{:?}", def_id).replace(|c: char| !c.is_alphanumeric(), "_");

                if let Some(attr) = self.node_styles.get(&def_id) {
                    writeln!(dot, "        {} [{}];", node_id, attr).unwrap();
                }
            }
            writeln!(dot, "    }}").unwrap();
        }

        for (from, to, edge_type) in &self.edges {
            let from_id = format!("n_{:?}", from).replace(|c: char| !c.is_alphanumeric(), "_");
            let to_id = format!("n_{:?}", to).replace(|c: char| !c.is_alphanumeric(), "_");

            let attr = match edge_type {
                UigEdge::CallerToCallee => "color=black, style=solid",
                UigEdge::ConsToMethod => "color=black, style=dotted",
                UigEdge::MutToCaller => "color=blue, style=dashed",
            };

            writeln!(dot, "    {} -> {} [{}];", from_id, to_id, attr).unwrap();
        }

        writeln!(dot, "}}").unwrap();
        dot
    }
}
