use crate::analysis::core::alias_analysis::default::types::TyKind;
use rustc_data_structures::fx::FxHashMap;

#[derive(Debug, Clone)]
pub struct ValueNode {
    pub index: usize, // node index; this could be the field of a value.
    pub local: usize, // This is the real local; The range of index is generally larger than local.
    pub need_drop: bool,
    pub may_drop: bool,
    pub kind: TyKind,
    pub father: usize,
    pub field_id: usize, // the field id of its father node.
    pub birth: isize,
    pub fields: FxHashMap<usize, usize>,
}

impl ValueNode {
    pub fn new(index: usize, local: usize, need_drop: bool, may_drop: bool) -> Self {
        ValueNode {
            index,
            local,
            need_drop,
            father: local,
            field_id: usize::MAX,
            birth: 0,
            may_drop,
            kind: TyKind::Adt,
            fields: FxHashMap::default(),
        }
    }

    pub fn drop(&mut self) {
        self.birth = -1;
    }

    pub fn is_dropped(&self) -> bool {
        !self.birth > -1
    }

    pub fn is_tuple(&self) -> bool {
        self.kind == TyKind::Tuple
    }

    pub fn is_ptr(&self) -> bool {
        self.kind == TyKind::RawPtr || self.kind == TyKind::Ref
    }

    pub fn is_ref(&self) -> bool {
        self.kind == TyKind::Ref
    }

    pub fn is_corner_case(&self) -> bool {
        self.kind == TyKind::CornerCase
    }
}
