use super::Config;
use super::dep_edge::DepEdge;
use super::dep_node::{DepNode, desc_str};
use super::transform::TransformKind;
use super::ty_wrapper::TyWrapper;
use crate::analysis::core::api_dependency::ApiDependencyGraph;
use crate::analysis::core::api_dependency::mono::Mono;
use crate::analysis::core::api_dependency::utils::{is_fuzzable_ty, ty_complexity};
use crate::analysis::core::api_dependency::visitor::FnVisitor;
use crate::analysis::core::api_dependency::{mono, utils};
use crate::utils::fs::rap_create_file;
use crate::{rap_debug, rap_info, rap_trace};
use petgraph::Direction::{self, Incoming};
use petgraph::Graph;
use petgraph::dot;
use petgraph::graph::NodeIndex;
use petgraph::visit::{NodeIndexable, Visitable};
use rand::Rng;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, GenericArgsRef, TraitRef, Ty, TyCtxt};
use rustc_span::sym::require;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;
use std::time;

fn add_return_type_if_reachable<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    reachable_tys: &HashSet<TyWrapper<'tcx>>,
    new_tys: &mut HashSet<Ty<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let fn_sig = utils::fn_sig_with_generic_args(fn_did, args, tcx);
    let inputs = fn_sig.inputs();
    for input_ty in inputs {
        if !is_fuzzable_ty(*input_ty, tcx) && !reachable_tys.contains(&TyWrapper::from(*input_ty)) {
            return false;
        }
    }
    let output_ty = fn_sig.output();
    if !output_ty.is_unit() {
        new_tys.insert(output_ty);
    }
    true
}

#[derive(Clone)]
struct TypeCandidates<'tcx> {
    tcx: TyCtxt<'tcx>,
    candidates: HashSet<TyWrapper<'tcx>>,
    max_complexity: usize,
}

impl<'tcx> TypeCandidates<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, max_complexity: usize) -> Self {
        TypeCandidates {
            tcx,
            candidates: HashSet::new(),
            max_complexity,
        }
    }

    pub fn insert(&mut self, ty: Ty<'tcx>) -> bool {
        if ty_complexity(ty) <= self.max_complexity {
            self.candidates.insert(ty.into())
        } else {
            false
        }
    }

    pub fn insert_all(&mut self, ty: Ty<'tcx>) -> bool {
        let complexity = ty_complexity(ty);
        self.insert_all_with_complexity(ty, complexity)
    }

    pub fn insert_all_with_complexity(&mut self, ty: Ty<'tcx>, current_cmplx: usize) -> bool {
        if current_cmplx > self.max_complexity {
            return false;
        }

        // add T
        let mut changed = self.candidates.insert(ty.into());

        // add &T
        changed |= self.insert_all_with_complexity(
            Ty::new_ref(
                self.tcx,
                self.tcx.lifetimes.re_erased,
                ty,
                ty::Mutability::Not,
            ),
            current_cmplx + 1,
        );

        // add &mut T
        changed |= self.insert_all_with_complexity(
            Ty::new_ref(
                self.tcx,
                self.tcx.lifetimes.re_erased,
                ty,
                ty::Mutability::Mut,
            ),
            current_cmplx + 1,
        );

        // add &[T]
        changed |= self.insert_all_with_complexity(
            Ty::new_ref(
                self.tcx,
                self.tcx.lifetimes.re_erased,
                Ty::new_slice(self.tcx, ty),
                ty::Mutability::Not,
            ),
            current_cmplx + 2,
        );

        // add &mut [T]
        changed |= self.insert_all_with_complexity(
            Ty::new_ref(
                self.tcx,
                self.tcx.lifetimes.re_erased,
                Ty::new_slice(self.tcx, ty),
                ty::Mutability::Mut,
            ),
            current_cmplx + 2,
        );

        changed
    }

    pub fn add_prelude_tys(&mut self) {
        let tcx = self.tcx;
        let prelude_tys = [
            tcx.types.bool,
            tcx.types.char,
            tcx.types.f32,
            tcx.types.f64,
            tcx.types.i8,
            tcx.types.i16,
            tcx.types.i32,
            tcx.types.i64,
            tcx.types.isize,
            tcx.types.u8,
            tcx.types.u16,
            tcx.types.u32,
            tcx.types.u64,
            tcx.types.usize,
            Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, tcx.types.str_),
        ];
        prelude_tys.into_iter().for_each(|ty| {
            self.insert_all(ty);
        });
    }

    pub fn candidates(&self) -> &HashSet<TyWrapper<'tcx>> {
        &self.candidates
    }
}

pub fn partion_generic_api<'tcx>(
    all_apis: &HashSet<DefId>,
    tcx: TyCtxt<'tcx>,
) -> (HashSet<DefId>, HashSet<DefId>) {
    let mut generic_api = HashSet::new();
    let mut non_generic_api = HashSet::new();
    for api_id in all_apis.iter() {
        if tcx.generics_of(*api_id).requires_monomorphization(tcx) {
            generic_api.insert(*api_id);
        } else {
            non_generic_api.insert(*api_id);
        }
    }
    (non_generic_api, generic_api)
}

impl<'tcx> ApiDependencyGraph<'tcx> {
    pub fn resolve_generic_api(&mut self) {
        rap_info!("start resolving generic APIs");
        let generic_map = self.search_reachable_apis();
        self.prune_by_similarity(generic_map);
    }

    pub fn search_reachable_apis(&mut self) -> HashMap<DefId, HashSet<Mono<'tcx>>> {
        let tcx = self.tcx;
        let max_ty_complexity = 6;
        let mut type_candidates = TypeCandidates::new(self.tcx, max_ty_complexity);

        type_candidates.add_prelude_tys();

        // let mut num_reachable = 0;
        let mut generic_map: HashMap<DefId, HashSet<Mono>> = HashMap::new();

        // initialize unreachable non generic API
        let (mut unreachable_non_generic_api, generic_apis) =
            partion_generic_api(&self.all_apis, tcx);

        rap_debug!("[resolve_generic] non_generic_api = {unreachable_non_generic_api:?}");
        rap_debug!("[resolve_generic] generic_api = {generic_apis:?}");

        let mut num_iter = 0;
        let max_iteration = 10;

        loop {
            num_iter += 1;
            let all_reachable_tys = type_candidates.candidates();
            rap_info!(
                "start iter #{num_iter}, # of reachble types = {}",
                all_reachable_tys.len()
            );

            // dump all reachable types to files, each line output a type
            let mut file = rap_create_file(Path::new("reachable_types.txt"), "create file fail");
            for ty in all_reachable_tys.iter() {
                writeln!(file, "{}", ty.ty()).unwrap();
            }

            let mut current_tys = HashSet::new();
            // check whether there is any non-generic api that is reachable
            // if the api is reachable, add output type to reachble_tys,
            // and remove fn_did from the set.
            unreachable_non_generic_api.retain(|fn_did| {
                !add_return_type_if_reachable(
                    *fn_did,
                    ty::GenericArgs::identity_for_item(tcx, *fn_did),
                    all_reachable_tys,
                    &mut current_tys,
                    tcx,
                )
            });

            // check each generic API for new monomorphic API
            for fn_did in generic_apis.iter() {
                let mono_set = mono::resolve_mono_apis(*fn_did, &all_reachable_tys, tcx);
                rap_debug!(
                    "[search_reachable_apis] {} -> {:?}",
                    tcx.def_path_str(*fn_did),
                    mono_set
                );
                for mono in mono_set.monos {
                    let fn_sig = utils::fn_sig_with_generic_args(*fn_did, &mono.value, tcx);
                    let output_ty = fn_sig.output();
                    if generic_map.entry(*fn_did).or_default().insert(mono) {
                        if !output_ty.is_unit() && ty_complexity(output_ty) <= max_ty_complexity {
                            current_tys.insert(output_ty);
                        }
                    }
                }
            }

            let mut changed = false;
            for ty in current_tys {
                changed = changed | type_candidates.insert_all(ty);
            }

            if !changed {
                rap_info!("Terminate. Reachable types unchange in this iteration.");
                break;
            }
            if num_iter >= max_iteration {
                rap_info!("Terminate. Max iteration reached.");
                break;
            }
        }

        let mono_cnt = generic_map.values().fold(0, |acc, monos| acc + monos.len());

        rap_debug!(
            "# of reachable types: {}",
            type_candidates.candidates().len()
        );
        rap_debug!("# of mono APIs: {}", mono_cnt);

        generic_map
    }

    pub fn prune_by_similarity(&mut self, generic_map: HashMap<DefId, HashSet<Mono<'tcx>>>) {
        let mut rng = rand::rng();
        let mut reserved_map: HashMap<DefId, Vec<(GenericArgsRef<'tcx>, bool)>> = HashMap::new();

        // transform into reserved map
        for (fn_did, mono_set) in generic_map {
            let entry = reserved_map.entry(fn_did).or_default();
            mono_set.into_iter().for_each(|mono| {
                let args = self.tcx.mk_args(&mono.value);
                self.add_api(fn_did, args);
                entry.push((args, false));
            });
        }
        // add transform edges
        self.update_transform_edges();

        self.dump_to_dot(Path::new("api_graph_unpruned.dot"), self.tcx);
        let (estimate, total) = self.estimate_coverage_distinct();
        rap_info!(
            "estimate API coverage before pruning: {:.2} ({}/{})",
            estimate as f64 / total as f64,
            estimate,
            total
        );

        let mut visited = vec![false; self.graph.node_count()];
        let mut reserved = vec![false; self.graph.node_count()];

        // initialize reserved
        // all non-generic API should be reserved
        for idx in self.graph.node_indices() {
            if let DepNode::Api(fn_did, _) = self.graph[idx] {
                if !utils::fn_requires_monomorphization(fn_did, self.tcx) {
                    reserved[idx.index()] = true;
                }
            }
        }

        // add all monomorphic APIs to API Graph, but select minimal set cover to be reserved
        for (fn_did, monos) in &mut reserved_map {
            select_minimal_set_cover(self.tcx, *fn_did, monos, &mut rng);
            for (args, r) in monos {
                if *r {
                    let idx = self.get_index(DepNode::Api(*fn_did, args)).unwrap();
                    reserved[idx.index()] = true;
                }
            }
        }

        // traverse from start node, if a node can achieve a reserved node,
        // this node should be reserved as well
        for node in self.graph.node_indices() {
            if !visited[node.index()] && self.is_start_node_index(node) {
                rap_trace!("start propagate from {:?}", self.graph[node]);
                self.propagate_reserved(node, &mut visited, &mut reserved);
            }
        }

        for node in self.graph.node_indices() {
            if !visited[node.index()] {
                rap_trace!("{:?} is unvisited", self.graph[node]);
                self.propagate_reserved(node, &mut visited, &mut reserved);
            }
        }

        let mut count = 0;
        for idx in (0..self.graph.node_count()).rev() {
            if !reserved[idx] {
                self.graph
                    .remove_node(NodeIndex::new(idx))
                    .expect("remove should not fail");
                count += 1;
            }
        }
        self.recache();
        rap_info!("remove {} nodes by pruning", count);
        let (estimate, total) = self.estimate_coverage_distinct();
        rap_info!(
            "estimate API coverage after pruning: {:.2} ({}/{})",
            estimate as f64 / total as f64,
            estimate,
            total
        );
    }

    fn recache(&mut self) {
        self.node_indices.clear();
        self.ty_nodes.clear();
        self.api_nodes.clear();
        for idx in self.graph.node_indices() {
            let node = &self.graph[idx];
            self.node_indices.insert(node.clone(), idx);
            match node {
                DepNode::Api(..) => self.api_nodes.push(idx),
                DepNode::Ty(..) => self.ty_nodes.push(idx),
                _ => {}
            }
        }
    }

    pub fn propagate_reserved(
        &self,
        node: NodeIndex,
        visited: &mut [bool],
        reserved: &mut [bool],
    ) -> bool {
        visited[node.index()] = true;

        match self.graph[node] {
            DepNode::Api(..) => {
                for neighbor in self.graph.neighbors(node) {
                    if !visited[neighbor.index()] {
                        reserved[node.index()] |=
                            self.propagate_reserved(neighbor, visited, reserved);
                    }
                }
            }
            DepNode::Ty(..) => {
                for neighbor in self.graph.neighbors(node) {
                    if !visited[neighbor.index()] {
                        self.propagate_reserved(neighbor, visited, reserved);
                    }
                    reserved[node.index()] |= reserved[neighbor.index()]
                }
            }
        }

        if reserved[node.index()] {
            rap_trace!(
                "[propagate_reserved] reserve: {:?}",
                self.graph.node_weight(node).unwrap()
            );
        }
        reserved[node.index()]
    }
}

fn select_minimal_set_cover<'tcx, 'a>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    monos: &'a mut Vec<(ty::GenericArgsRef<'tcx>, bool)>,
    rng: &mut impl Rng,
) {
    rap_debug!("select minimal set for: {}", tcx.def_path_str(fn_did));
    let mut impl_vec = Vec::new();
    for (args, _) in monos.iter() {
        let impls = mono::get_impls(tcx, fn_did, args);
        impl_vec.push(impls);
    }

    let mut selected_cnt = 0;
    let mut complete = HashSet::new();
    loop {
        let mut current_max = 0;
        let mut idx = 0;
        for i in 0..impl_vec.len() {
            let impls = &impl_vec[i];
            let size = impls.iter().fold(0, |cnt, did| {
                if !complete.contains(did) {
                    cnt + 1
                } else {
                    cnt
                }
            });
            if size > current_max {
                current_max = size;
                idx = i;
            }
        }
        if current_max == 0 {
            break;
        }
        selected_cnt += 1;
        monos[idx].1 = true;
        rap_debug!("select: {:?}", monos[idx].0);
        impl_vec[idx].iter().for_each(|did| {
            complete.insert(*did);
        });
    }

    if selected_cnt == 0 {
        let idx = rng.random_range(0..impl_vec.len());
        rap_debug!("random select: {:?}", monos[idx].0);
        monos[idx].1 = true;
    }
}
