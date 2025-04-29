pub mod checking;
pub mod data_collection;
pub mod iterator;
pub mod memory_cloning;

use rustc_middle::ty::TyCtxt;

use super::core::dataflow::{graph::Graph, DataFlow};
use checking::bounds_checking::BoundsCheck;
use checking::encoding_checking::EncodingCheck;
use data_collection::initialization::InitializationCheck;
use data_collection::reservation::ReservationCheck;
use data_collection::suboptimal::SuboptimalCheck;
use iterator::next_iterator::NextIteratorCheck;
use memory_cloning::hash_key_cloning::HashKeyCloningCheck;
use memory_cloning::used_as_immutable::UsedAsImmutableCheck;

use lazy_static::lazy_static;
use rustc_span::symbol::Symbol;
use std::sync::Mutex;

lazy_static! {
    pub static ref NO_STD: Mutex<bool> = Mutex::new(false);
    pub static ref LEVEL: Mutex<usize> = Mutex::new(0);
}

pub struct Opt<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub level: usize,
}

pub trait OptCheck {
    fn new() -> Self;
    fn check(&mut self, graph: &Graph, tcx: &TyCtxt);
    fn report(&self, graph: &Graph);
}

impl<'tcx> Opt<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, level: usize) -> Self {
        Self { tcx, level }
    }

    fn has_crate(&self, name: &str) -> bool {
        for num in self.tcx.crates(()) {
            if self.tcx.crate_name(*num) == Symbol::intern(name) {
                return true;
            }
        }
        false
    }

    pub fn start(&mut self) {
        let mut dataflow = DataFlow::new(self.tcx, false);
        dataflow.build_graphs();
        {
            let mut no_std = NO_STD.lock().unwrap();
            *no_std = !self.has_crate("std");
            let mut level = LEVEL.lock().unwrap();
            *level = self.level;
        }
        if !self.has_crate("core") {
            //core it self
            return;
        }

        dataflow.graphs.iter().for_each(|(_, graph)| {
            let mut bounds_check = BoundsCheck::new();
            bounds_check.check(graph, &self.tcx);
            bounds_check.report(graph);

            let no_std = NO_STD.lock().unwrap();
            if !*no_std {
                let mut encoding_check = EncodingCheck::new();
                encoding_check.check(graph, &self.tcx);
                encoding_check.report(graph);

                let mut suboptimal_check = SuboptimalCheck::new();
                suboptimal_check.check(graph, &self.tcx);
                suboptimal_check.report(graph);

                let mut initialization_check = InitializationCheck::new();
                initialization_check.check(graph, &self.tcx);
                initialization_check.report(graph);

                let mut reservation_check = ReservationCheck::new();
                reservation_check.check(graph, &self.tcx);
                reservation_check.report(graph);

                let mut hash_key_cloning_check = HashKeyCloningCheck::new();
                hash_key_cloning_check.check(graph, &self.tcx);
                hash_key_cloning_check.report(graph);

                let mut used_as_immutable_check = UsedAsImmutableCheck::new();
                used_as_immutable_check.check(graph, &self.tcx);
                used_as_immutable_check.report(graph);

                let mut next_iterator_check = NextIteratorCheck::new();
                next_iterator_check.check(graph, &self.tcx);
                if next_iterator_check.valid {
                    next_iterator_check.report(graph);
                }
            }
        });
    }
}
