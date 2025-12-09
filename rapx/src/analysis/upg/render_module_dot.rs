use std::{
    collections::{HashMap, HashSet},
    fmt::Write,
};

use super::{
    UPGAnalysis,
    upg_unit::{UPGEdge, UPGNode, UPGUnit},
};
use crate::analysis::utils::{draw_dot::render_dot_graphs, fn_info::*};
use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::ty::TyCtxt;

impl<'tcx> UPGAnalysis<'tcx> {
    /// Main function to aggregate data and render DOT graphs per module.
    pub fn render_module_dot(&self) {
        let mut modules_data: HashMap<String, ModuleGraphData> = HashMap::new();

        let mut collect_unit = |unit: &UPGUnit| {
            let caller_id = unit.caller.def_id;
            let module_name = self.get_module_name(caller_id);

            let module_data = modules_data
                .entry(module_name)
                .or_insert_with(ModuleGraphData::new);

            module_data.add_node(self.tcx, unit.caller, None);

            if let Some(adt) = get_adt_via_method(self.tcx, caller_id) {
                if adt.literal_cons_enabled {
                    let adt_node_type = FnInfo::new(adt.def_id, Safety::Safe, FnKind::Constructor);
                    let label = format!("Literal Constructor: {}", self.tcx.item_name(adt.def_id));
                    module_data.add_node(self.tcx, adt_node_type, Some(label));
                    if unit.caller.fn_kind == FnKind::Method {
                        module_data.add_edge(adt.def_id, caller_id, UPGEdge::ConsToMethod);
                    }
                } else {
                    let adt_node_type = FnInfo::new(adt.def_id, Safety::Safe, FnKind::Method);
                    let label = format!(
                        "MutMethod Introduced by PubFields: {}",
                        self.tcx.item_name(adt.def_id)
                    );
                    module_data.add_node(self.tcx, adt_node_type, Some(label));
                    if unit.caller.fn_kind == FnKind::Method {
                        module_data.add_edge(adt.def_id, caller_id, UPGEdge::MutToCaller);
                    }
                }
            }

            // Edge from associated item (constructor) to the method.
            for cons in &unit.caller_cons {
                module_data.add_node(self.tcx, *cons, None);
                module_data.add_edge(cons.def_id, unit.caller.def_id, UPGEdge::ConsToMethod);
            }

            // Edge from mutable access to the caller.
            for mut_method_id in &unit.mut_methods {
                let node_type = get_type(self.tcx, *mut_method_id);
                let fn_safety = check_safety(self.tcx, *mut_method_id);
                let node = FnInfo::new(*mut_method_id, fn_safety, node_type);

                module_data.add_node(self.tcx, node, None);
                module_data.add_edge(*mut_method_id, unit.caller.def_id, UPGEdge::MutToCaller);
            }

            // Edge representing a call from caller to callee.
            for callee in &unit.callees {
                module_data.add_node(self.tcx, *callee, None);
                module_data.add_edge(unit.caller.def_id, callee.def_id, UPGEdge::CallerToCallee);
            }

            rap_debug!("raw ptrs: {:?}", unit.raw_ptrs);
            if !unit.raw_ptrs.is_empty() {
                let all_raw_ptrs = unit
                    .raw_ptrs
                    .iter()
                    .map(|p| format!("{:?}", p))
                    .collect::<Vec<_>>()
                    .join(", ");

                match get_ptr_deref_dummy_def_id(self.tcx) {
                    Some(dummy_fn_def_id) => {
                        let rawptr_deref_fn =
                            FnInfo::new(dummy_fn_def_id, Safety::Unsafe, FnKind::Intrinsic);
                        module_data.add_node(
                            self.tcx,
                            rawptr_deref_fn,
                            Some(format!("Raw ptr deref: {}", all_raw_ptrs)),
                        );
                        module_data.add_edge(
                            unit.caller.def_id,
                            dummy_fn_def_id,
                            UPGEdge::CallerToCallee,
                        );
                    }
                    None => {
                        rap_info!("fail to find the dummy ptr deref id.");
                    }
                }
            }

            rap_debug!("static muts: {:?}", unit.static_muts);
            for def_id in &unit.static_muts {
                let node = FnInfo::new(*def_id, Safety::Unsafe, FnKind::Intrinsic);
                module_data.add_node(self.tcx, node, None);
                module_data.add_edge(unit.caller.def_id, *def_id, UPGEdge::CallerToCallee);
            }
        };

        // Aggregate all Units
        for upg in &self.upgs {
            collect_unit(upg);
        }

        // Generate string of dot
        let mut final_dots = Vec::new();
        for (mod_name, data) in modules_data {
            let dot = data.upg_unit_string(&mod_name);
            final_dots.push((mod_name, dot));
        }
        rap_info!("{:?}", final_dots); // Output required for tests; do not change.
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
    structs: HashMap<String, HashSet<FnInfo>>,
    // Edges between DefIds with their type.
    edges: HashSet<(DefId, DefId, UPGEdge)>,
    // Pre-generated DOT attribute strings for each node (DefId).
    node_styles: HashMap<DefId, String>,
}

impl ModuleGraphData {
    fn new() -> Self {
        Self {
            structs: HashMap::new(),
            edges: HashSet::new(),
            node_styles: HashMap::new(),
        }
    }

    fn add_node(&mut self, tcx: TyCtxt<'_>, node: FnInfo, custom_label: Option<String>) {
        let adt_name = self.get_adt_name(tcx, node.def_id);
        self.structs.entry(adt_name).or_default().insert(node);

        if !self.node_styles.contains_key(&node.def_id) || custom_label.is_some() {
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

            self.node_styles.insert(node.def_id, attr);
        }
    }

    fn add_edge(&mut self, from: DefId, to: DefId, edge_type: UPGEdge) {
        if from == to {
            return;
        }
        self.edges.insert((from, to, edge_type));
    }

    fn get_adt_name(&self, tcx: TyCtxt<'_>, def_id: DefId) -> String {
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

    fn upg_unit_string(&self, module_name: &str) -> String {
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
