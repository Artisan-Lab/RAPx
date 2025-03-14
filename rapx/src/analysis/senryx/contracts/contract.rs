use super::abstract_state::*;
use crate::analysis::senryx::contracts::state_lattice::Lattice;

#[derive(Debug, PartialEq, Clone)]
pub enum Contract<'tcx> {
    ValueCheck { op: Op, value: Value },
    StateCheck { op: Op, state: StateType<'tcx> },
}

pub fn check_contract<'tcx>(
    contract: &Contract<'tcx>,
    abstate_item: &AbstractStateItem<'tcx>,
) -> bool {
    match contract {
        Contract::ValueCheck { op, value } => {
            return handle_value_op(&abstate_item.value, op, value);
        }
        Contract::StateCheck { op: _, state } => {
            for ab_state in &abstate_item.state {
                if check_is_same_state_type(ab_state, &state) && !ab_state.check() {
                    return false;
                }
                // if check_is_same_state_type(ab_state, &state)
                //     && handle_state_op(ab_state, op, state)
                // {
                //     return true;
                // }
            }
            return true;
        }
    }
}

pub fn check_is_same_state_type(left: &StateType, right: &StateType) -> bool {
    match (left, right) {
        (StateType::AllocatedState(_), StateType::AllocatedState(_)) => {
            return true;
        }
        (StateType::AlignState(_), StateType::AlignState(_)) => {
            return true;
        }
        _ => false,
    }
}

pub fn handle_value_op<T: std::cmp::PartialEq + std::cmp::PartialOrd>(
    left: &(T, T),
    op: &Op,
    right: &T,
) -> bool {
    match op {
        Op::EQ => {
            return left.0 == *right;
        }
        Op::NE => {
            return left.0 != *right;
        }
        Op::LT => {
            return left.1 < *right;
        }
        Op::GT => {
            return left.0 > *right;
        }
        Op::LE => {
            return left.1 <= *right;
        }
        Op::GE => {
            return left.0 >= *right;
        }
    }
}

pub fn handle_state_op<'tcx>(left: &StateType<'tcx>, op: &Op, right: &StateType<'tcx>) -> bool {
    match op {
        Op::LT => left.less_than(right.clone()),
        Op::LE => left.less_than(right.clone()) || left.equal(right.clone()),
        Op::GT => right.less_than(left.clone()),
        Op::GE => right.less_than(left.clone()) || right.equal(left.clone()),
        Op::EQ => left.equal(right.clone()),
        Op::NE => !left.equal(right.clone()),
    }
}
