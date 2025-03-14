use super::abstract_state::*;
use super::contract::*;
use core::mem;
use std::collections::HashMap;
use std::marker::PhantomData;

pub trait Checker<'tcx> {
    fn variable_contracts(&self) -> &HashMap<usize, Vec<Contract<'tcx>>>;
}

pub struct SliceFromRawPartsChecker<'tcx, T> {
    pub variable_contracts: HashMap<usize, Vec<Contract<'tcx>>>,
    _marker: PhantomData<T>,
}

impl<'tcx, T> Checker<'tcx> for SliceFromRawPartsChecker<'tcx, T> {
    fn variable_contracts(&self) -> &HashMap<usize, Vec<Contract<'tcx>>> {
        &self.variable_contracts
    }
}

impl<'tcx, T> SliceFromRawPartsChecker<'tcx, T> {
    pub fn new() -> Self {
        let mut map = HashMap::new();
        map.insert(
            0,
            vec![
                // Contract::StateCheck {
                //     op: Op::GE,
                //     state: StateType::AllocatedState(AllocatedState::Alloc),
                // },
                Contract::StateCheck {
                    op: Op::GT,
                    state: StateType::AlignState(AlignState::Unaligned),
                },
            ],
        );
        map.insert(
            1,
            vec![Contract::ValueCheck {
                op: Op::LE,
                value: Value::Usize((isize::MAX as usize) / mem::size_of::<T>()),
            }],
        );
        Self {
            variable_contracts: map,
            _marker: PhantomData,
        }
    }
}
