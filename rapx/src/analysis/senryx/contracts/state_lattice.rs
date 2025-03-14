use crate::rap_info;

use super::abstract_state::*;

pub trait Lattice {
    fn join(&self, other: Self) -> Self;
    fn meet(&self, other: Self) -> Self;
    fn less_than(&self, other: Self) -> bool;
    fn equal(&self, other: Self) -> bool;
    fn check(&self) -> bool;
}

impl<'tcx> Lattice for StateType<'tcx> {
    fn join(&self, other: Self) -> Self {
        match &self {
            &StateType::AllocatedState(a) => match other {
                StateType::AllocatedState(b) => StateType::AllocatedState(a.join(b)),
                _ => panic!("Incompatible types"),
            },
            &StateType::AlignState(a) => match other {
                StateType::AlignState(b) => StateType::AlignState(a.join(b)),
                _ => panic!("Incompatible types"),
            },
        }
    }

    fn meet(&self, other: Self) -> Self {
        match &self {
            &StateType::AllocatedState(a) => match other {
                StateType::AllocatedState(b) => StateType::AllocatedState(a.meet(b)),
                _ => panic!("Incompatible types"),
            },
            &StateType::AlignState(a) => match other {
                StateType::AlignState(b) => StateType::AlignState(a.meet(b)),
                _ => panic!("Incompatible types"),
            },
        }
    }

    fn less_than(&self, other: Self) -> bool {
        match &self {
            &StateType::AllocatedState(a) => match other {
                StateType::AllocatedState(b) => a.less_than(b),
                _ => panic!("Incompatible types"),
            },
            &StateType::AlignState(a) => match other {
                StateType::AlignState(b) => a.less_than(b),
                _ => panic!("Incompatible types"),
            },
        }
    }

    fn equal(&self, other: Self) -> bool {
        match &self {
            &StateType::AllocatedState(a) => match other {
                StateType::AllocatedState(b) => a.equal(b),
                _ => panic!("Incompatible types"),
            },
            &StateType::AlignState(a) => match other {
                StateType::AlignState(b) => a.equal(b),
                _ => panic!("Incompatible types"),
            },
        }
    }

    fn check(&self) -> bool {
        match &self {
            &StateType::AllocatedState(a) => a.check(),
            &StateType::AlignState(a) => a.check(),
        }
    }
}

impl Lattice for AllocatedState {
    fn join(&self, other: Self) -> Self {
        match (*self, other) {
            (AllocatedState::Bottom, _) => other,
            (_, AllocatedState::Bottom) => *self,
            (AllocatedState::Top, _) | (_, AllocatedState::Top) => AllocatedState::Top,
            (AllocatedState::Borrowed, AllocatedState::Moved)
            | (AllocatedState::Moved, AllocatedState::Borrowed) => AllocatedState::Top,
            (AllocatedState::Alloc, AllocatedState::SpecificAlloc)
            | (AllocatedState::SpecificAlloc, AllocatedState::Alloc) => {
                AllocatedState::SpecificAlloc
            }
            (state1, state2) if state1 == state2 => state1,
            (AllocatedState::Alloc, AllocatedState::Borrowed)
            | (AllocatedState::Borrowed, AllocatedState::Alloc) => AllocatedState::Borrowed,
            (AllocatedState::Alloc, AllocatedState::Moved)
            | (AllocatedState::Moved, AllocatedState::Alloc) => AllocatedState::Moved,
            (AllocatedState::SpecificAlloc, AllocatedState::Borrowed)
            | (AllocatedState::Borrowed, AllocatedState::SpecificAlloc) => AllocatedState::Borrowed,
            (AllocatedState::Moved, AllocatedState::SpecificAlloc)
            | (AllocatedState::SpecificAlloc, AllocatedState::Moved) => AllocatedState::Moved,
            _ => AllocatedState::Top,
        }
    }

    fn meet(&self, other: Self) -> Self {
        match (*self, other) {
            (AllocatedState::Top, _) => other,
            (_, AllocatedState::Top) => *self,
            (AllocatedState::Bottom, _) | (_, AllocatedState::Bottom) => AllocatedState::Bottom,
            (AllocatedState::Borrowed, AllocatedState::Moved)
            | (AllocatedState::Moved, AllocatedState::Borrowed) => AllocatedState::Bottom,
            (AllocatedState::Alloc, AllocatedState::SpecificAlloc)
            | (AllocatedState::SpecificAlloc, AllocatedState::Alloc) => AllocatedState::Alloc,
            (state1, state2) if state1 == state2 => state1,
            (AllocatedState::Alloc, AllocatedState::Borrowed)
            | (AllocatedState::Borrowed, AllocatedState::Alloc) => AllocatedState::Alloc,
            (AllocatedState::SpecificAlloc, AllocatedState::Borrowed)
            | (AllocatedState::Borrowed, AllocatedState::SpecificAlloc) => {
                AllocatedState::SpecificAlloc
            }
            (AllocatedState::Moved, AllocatedState::SpecificAlloc)
            | (AllocatedState::SpecificAlloc, AllocatedState::Moved) => {
                AllocatedState::SpecificAlloc
            }
            _ => AllocatedState::Bottom,
        }
    }

    fn less_than(&self, other: Self) -> bool {
        match (*self, other) {
            (AllocatedState::Bottom, _) | (_, AllocatedState::Top) => true,
            (AllocatedState::Alloc, AllocatedState::Borrowed) => true,
            (AllocatedState::Alloc, AllocatedState::SpecificAlloc) => true,
            (AllocatedState::Alloc, AllocatedState::Moved) => true,
            (AllocatedState::SpecificAlloc, AllocatedState::Borrowed) => true,
            (AllocatedState::SpecificAlloc, AllocatedState::Moved) => true,
            _ => false,
        }
    }

    fn equal(&self, other: Self) -> bool {
        *self == other
    }

    fn check(&self) -> bool {
        true
    }
}

impl<'tcx> Lattice for AlignState<'tcx> {
    fn join(&self, other: Self) -> Self {
        match (self, other.clone()) {
            (AlignState::Aligned, _) => AlignState::Aligned,
            (AlignState::Cast(_, _), AlignState::Cast(_, _)) => AlignState::Unaligned,
            (AlignState::Unaligned, _) => AlignState::Unaligned,
            (_, AlignState::Unaligned) => AlignState::Unaligned,
            _ => other.clone(),
        }
    }

    fn meet(&self, other: Self) -> Self {
        other
        // match (self, other) {
        //     (AlignState::Aligned, _) => other,
        //     (AlignState::Big2SmallCast(_,_), AlignState::Big2SmallCast(_,_)) => AlignState::Aligned,
        //     (AlignState::Big2SmallCast(_,_), AlignState::Small2BigCast(_,_)) => AlignState::Unaligned,
        //     (AlignState::Big2SmallCast(_,_), AlignState::Aligned) => AlignState::Big2SmallCast(_,_),
        //     (AlignState::Small2BigCast, _) => AlignState::Small2BigCast,
        // }
    }

    fn less_than(&self, other: Self) -> bool {
        match (self, other) {
            (_, AlignState::Aligned) => true,
            (AlignState::Cast(_, _), AlignState::Cast(_, _)) => true,
            _ => false,
        }
    }

    fn equal(&self, other: Self) -> bool {
        *self == other
    }

    fn check(&self) -> bool {
        match self {
            AlignState::Aligned => true,
            AlignState::Unaligned => false,
            AlignState::Cast(src, dest) => {
                // rap_info!("src ty {:?}, dst ty {:?}",src, dest);
                let src_aligns = src.possible_aligns();
                let dest_aligns = dest.possible_aligns();
                if dest_aligns.len() == 0 && src != dest {
                    // dst ty could be arbitrary type && src and dst are different types
                    return false;
                }

                for &d_align in &dest_aligns {
                    if d_align != 1 && src_aligns.len() == 0 {
                        // src ty could be arbitrary type
                        return false;
                    }
                    for &s_align in &src_aligns {
                        if s_align > d_align {
                            return false;
                        }
                    }
                }
                true
            }
        }
    }
}

impl Lattice for InitState {
    fn join(&self, other: Self) -> Self {
        match (self, other) {
            (InitState::FullyInitialized, _) => InitState::FullyInitialized,
            (_, InitState::FullyInitialized) => InitState::FullyInitialized,
            _ => InitState::PartlyInitialized,
        }
    }

    fn meet(&self, other: Self) -> Self {
        match (self, other) {
            (InitState::FullyInitialized, _) => other,
            (_, InitState::FullyInitialized) => *self,
            _ => InitState::PartlyInitialized,
        }
    }

    fn less_than(&self, other: Self) -> bool {
        match (self, other) {
            (InitState::FullyInitialized, InitState::FullyInitialized) => true,
            (InitState::PartlyInitialized, _) => true,
            _ => false,
        }
    }

    fn equal(&self, other: Self) -> bool {
        *self == other
    }

    fn check(&self) -> bool {
        true
    }
}
