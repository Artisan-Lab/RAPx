extern crate rustc_mir_dataflow;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{Body, CallReturnPlaces, Local, Location, Place, Statement, Terminator, TerminatorEdges},
    ty::TyCtxt,
};
use rustc_mir_dataflow::{Analysis, JoinSemiLattice};
use std::cell::RefCell;
use std::rc::Rc;

use super::super::{FnAliasMap, FnAliasPairs};

/// Place identifier supporting field-sensitive analysis
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceId {
    /// A local variable (e.g., _1)
    Local(usize),
    /// A field projection (e.g., _1.0)
    Field {
        base: Box<PlaceId>,
        field_idx: usize,
    },
}

impl PlaceId {
    /// Get the root local of this place
    pub fn root_local(&self) -> usize {
        match self {
            PlaceId::Local(idx) => *idx,
            PlaceId::Field { base, .. } => base.root_local(),
        }
    }

    /// Create a field projection
    pub fn project_field(&self, field_idx: usize) -> PlaceId {
        PlaceId::Field {
            base: Box::new(self.clone()),
            field_idx,
        }
    }
}

/// Information about all places in a function
#[derive(Clone)]
pub struct PlaceInfo<'tcx> {
    /// Mapping from PlaceId to index
    place_to_index: FxHashMap<PlaceId, usize>,
    /// Mapping from index to PlaceId
    index_to_place: Vec<PlaceId>,
    /// Mapping from PlaceId to MIR Place (when available)
    place_to_mir: FxHashMap<PlaceId, Place<'tcx>>,
    /// Whether each place may need drop
    may_drop: Vec<bool>,
    /// Whether each place needs drop
    need_drop: Vec<bool>,
    /// Total number of places
    num_places: usize,
}

impl<'tcx> PlaceInfo<'tcx> {
    /// Create a new PlaceInfo with initial capacity
    pub fn new() -> Self {
        PlaceInfo {
            place_to_index: FxHashMap::default(),
            index_to_place: Vec::new(),
            place_to_mir: FxHashMap::default(),
            may_drop: Vec::new(),
            need_drop: Vec::new(),
            num_places: 0,
        }
    }

    /// Register a new place and return its index
    pub fn register_place(&mut self, place_id: PlaceId, may_drop: bool, need_drop: bool) -> usize {
        if let Some(&idx) = self.place_to_index.get(&place_id) {
            return idx;
        }

        let idx = self.num_places;
        self.place_to_index.insert(place_id.clone(), idx);
        self.index_to_place.push(place_id);
        self.may_drop.push(may_drop);
        self.need_drop.push(need_drop);
        self.num_places += 1;
        idx
    }

    /// Get the index of a place
    pub fn get_index(&self, place_id: &PlaceId) -> Option<usize> {
        self.place_to_index.get(place_id).copied()
    }

    /// Get the PlaceId for an index
    pub fn get_place(&self, idx: usize) -> Option<&PlaceId> {
        self.index_to_place.get(idx)
    }

    /// Check if a place may drop
    pub fn may_drop(&self, idx: usize) -> bool {
        self.may_drop.get(idx).copied().unwrap_or(false)
    }

    /// Check if a place needs drop
    pub fn need_drop(&self, idx: usize) -> bool {
        self.need_drop.get(idx).copied().unwrap_or(false)
    }

    /// Get total number of places
    pub fn num_places(&self) -> usize {
        self.num_places
    }

    /// Associate a MIR place with a PlaceId
    pub fn associate_mir_place(&mut self, place_id: PlaceId, mir_place: Place<'tcx>) {
        self.place_to_mir.insert(place_id, mir_place);
    }
}

/// Alias domain using Union-Find data structure
#[derive(Clone, PartialEq, Eq)]
pub struct AliasDomain {
    /// Parent array for Union-Find
    parent: Vec<usize>,
    /// Rank for path compression
    rank: Vec<usize>,
}

impl AliasDomain {
    /// Create a new domain with n places
    pub fn new(num_places: usize) -> Self {
        AliasDomain {
            parent: (0..num_places).collect(),
            rank: vec![0; num_places],
        }
    }

    /// Find the representative of a place (with path compression)
    pub fn find(&mut self, idx: usize) -> usize {
        if self.parent[idx] != idx {
            self.parent[idx] = self.find(self.parent[idx]);
        }
        self.parent[idx]
    }

    /// Union two places (returns true if they were not already aliased)
    pub fn union(&mut self, idx1: usize, idx2: usize) -> bool {
        let root1 = self.find(idx1);
        let root2 = self.find(idx2);

        if root1 == root2 {
            return false;
        }

        // Union by rank
        if self.rank[root1] < self.rank[root2] {
            self.parent[root1] = root2;
        } else if self.rank[root1] > self.rank[root2] {
            self.parent[root2] = root1;
        } else {
            self.parent[root2] = root1;
            self.rank[root1] += 1;
        }

        true
    }

    /// Check if two places are aliased
    pub fn are_aliased(&mut self, idx1: usize, idx2: usize) -> bool {
        self.find(idx1) == self.find(idx2)
    }

    /// Remove all aliases for a place (used in kill phase)
    pub fn remove_aliases(&mut self, idx: usize) {
        // Make the place its own representative
        self.parent[idx] = idx;
        self.rank[idx] = 0;
    }

    /// Get all alias pairs (for debugging/summary extraction)
    pub fn get_all_alias_pairs(&self) -> Vec<(usize, usize)> {
        let mut pairs = Vec::new();
        let mut domain_clone = self.clone();

        for i in 0..self.parent.len() {
            for j in (i + 1)..self.parent.len() {
                if domain_clone.are_aliased(i, j) {
                    pairs.push((i, j));
                }
            }
        }

        pairs
    }
}

impl JoinSemiLattice for AliasDomain {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;

        // Get all alias pairs from other and union them in self
        let pairs = other.get_all_alias_pairs();
        for (i, j) in pairs {
            if self.union(i, j) {
                changed = true;
            }
        }

        changed
    }
}

/// Intraprocedural alias analyzer
pub struct FnAliasAnalyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'tcx Body<'tcx>,
    def_id: DefId,
    place_info: PlaceInfo<'tcx>,
    /// Function summaries for interprocedural analysis
    fn_summaries: Rc<RefCell<FnAliasMap>>,
}

impl<'tcx> FnAliasAnalyzer<'tcx> {
    /// Create a new analyzer for a function
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        body: &'tcx Body<'tcx>,
        fn_summaries: Rc<RefCell<FnAliasMap>>,
    ) -> Self {
        let place_info = PlaceInfo::new();
        FnAliasAnalyzer {
            tcx,
            body,
            def_id,
            place_info,
            fn_summaries,
        }
    }

    /// Get the place info
    pub fn place_info(&self) -> &PlaceInfo<'tcx> {
        &self.place_info
    }
}

// Implement Analysis for FnAliasAnalyzer
impl<'tcx> Analysis<'tcx> for FnAliasAnalyzer<'tcx> {
    type Domain = AliasDomain;

    const NAME: &'static str = "FnAliasAnalyzer";

    fn bottom_value(&self, _body: &Body<'tcx>) -> Self::Domain {
        // Bottom is no aliases
        AliasDomain::new(self.place_info.num_places())
    }

    fn initialize_start_block(&self, _body: &Body<'tcx>, _state: &mut Self::Domain) {
        // Entry state: no initial aliases between parameters
    }

    fn apply_primary_statement_effect(
        &self,
        _state: &mut Self::Domain,
        _statement: &Statement<'tcx>,
        _location: Location,
    ) {
        // TODO: Apply transfer functions for statements
    }

    fn apply_primary_terminator_effect<'mir>(
        &self,
        _state: &mut Self::Domain,
        _terminator: &'mir Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        // TODO: Apply transfer functions for terminators
        TerminatorEdges::None
    }

    fn apply_call_return_effect(
        &self,
        _state: &mut Self::Domain,
        _block: rustc_middle::mir::BasicBlock,
        _return_places: CallReturnPlaces<'_, 'tcx>,
    ) {
        // TODO: Handle call return effects
    }
}
