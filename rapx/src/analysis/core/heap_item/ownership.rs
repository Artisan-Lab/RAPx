use super::{DefaultOwnership, OwnershipLayout};
use rustc_middle::ty::Ty;
use std::fmt;
use std::fmt::Debug;

#[repr(u8)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum RawTypeOwner {
    Unowned = 0,
    Owned = 1,
    Uninit = 2,
}

impl Default for RawTypeOwner {
    fn default() -> Self {
        Self::Uninit
    }
}

impl RawTypeOwner {
    pub fn is_owned(&self) -> bool {
        match self {
            RawTypeOwner::Owned => true,
            RawTypeOwner::Unowned => false,
            RawTypeOwner::Uninit => false,
        }
    }
}

impl fmt::Display for RawTypeOwner {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = match self {
            RawTypeOwner::Unowned => "0",
            RawTypeOwner::Owned => "1",
            RawTypeOwner::Uninit => "2",
        };
        write!(f, "{}", name)
    }
}

pub enum TypeOwner<'tcx> {
    Owned(Ty<'tcx>),
    Unowned,
}

#[derive(Clone, Debug)]
pub struct OwnershipLayoutResult {
    layout: OwnershipLayout,
    param: bool,
    requirement: bool,
    owned: bool,
}

impl OwnershipLayoutResult {
    pub fn new() -> Self {
        Self {
            layout: Vec::new(),
            param: false,
            requirement: false,
            owned: false,
        }
    }

    pub fn layout(&self) -> &OwnershipLayout {
        &self.layout
    }

    pub fn layout_mut(&mut self) -> &mut OwnershipLayout {
        &mut self.layout
    }

    pub fn get_param(&self) -> bool {
        self.param
    }

    pub fn set_param(&mut self, p: bool) {
        self.param = p;
    }

    pub fn is_param_true(&self) -> bool {
        self.param == true
    }

    pub fn get_requirement(&self) -> bool {
        self.requirement
    }

    pub fn set_requirement(&mut self, r: bool) {
        self.requirement = r;
    }

    pub fn is_requirement_true(&self) -> bool {
        self.requirement == true
    }

    pub fn is_empty(&self) -> bool {
        self.layout.is_empty()
    }

    pub fn is_owned(&self) -> bool {
        self.owned == true
    }

    pub fn set_owned(&mut self, o: bool) {
        self.owned = o;
    }

    pub fn update_from_default_ownership_visitor<'tcx, 'a>(
        &mut self,
        default_ownership: &mut DefaultOwnership<'tcx, 'a>,
    ) {
        if default_ownership.is_owning_true() || default_ownership.is_ptr_true() {
            self.set_requirement(true);
        }

        if default_ownership.is_owning_true() {
            self.set_owned(true);
        }

        self.layout_mut().push(default_ownership.get_res());

        self.set_param(default_ownership.get_param());
    }
}
