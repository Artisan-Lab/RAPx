use crate::{
    analysis::utils::fn_info::{
        access_ident_recursive, match_ty_with_ident, parse_expr_into_local_and_ty,
        parse_expr_into_number,
    },
    rap_error,
};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp;
use rustc_middle::ty::Ty;
use rustc_middle::ty::TyCtxt;
use safety_parser::{safety::TagNameType, syn::Expr};

#[derive(Clone, Debug)]
pub enum CisRangeItem {
    Var(usize, Vec<usize>),
    Value(usize),
    Unknown,
}

impl CisRangeItem {
    pub fn get_var_base(&self) -> Option<usize> {
        match self {
            Self::Var(base, _) => Some(*base),
            _ => None,
        }
    }

    pub fn new_var(base: usize) -> Self {
        Self::Var(base, Vec::new())
    }

    pub fn new_value(value: usize) -> Self {
        Self::Value(value)
    }

    pub fn new_unknown() -> Self {
        Self::Unknown
    }
}

#[derive(Clone, Debug)]
pub struct CisRange {
    pub bin_op: BinOp,
    pub range: CisRangeItem,
}

impl CisRange {
    pub fn new(bin_op: BinOp, range: CisRangeItem) -> Self {
        Self { bin_op, range }
    }
}

#[derive(Clone, Debug)]
pub enum PropertyContract<'tcx> {
    // Align (ty)
    Align(Ty<'tcx>),
    Size(),
    NoPadding,
    NonNull,
    // Allocated( ty, length)
    Allocated(Ty<'tcx>, CisRangeItem),
    // InBound( ty, length)
    InBound(Ty<'tcx>, CisRangeItem),
    NonOverlap,
    ValidNum(CisRange),
    ValidString,
    ValidCStr,
    // Init( ty, length)
    Init(Ty<'tcx>, CisRangeItem),
    Unwrap,
    Typed(Ty<'tcx>),
    Owning,
    Alias,
    Alive,
    Pinned,
    NonVolatile,
    Opened,
    Trait,
    Unreachable,
    ValidPtr(Ty<'tcx>, CisRangeItem),
    Deref,
    Ptr2Ref,
    Layout,
    Unknown,
}

impl<'tcx> PropertyContract<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &Vec<Expr>) -> Self {
        match name {
            "Align" => {
                Self::check_arg_length(exprs.len(), 2, "Align");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Align");
                Self::Align(ty)
            }
            "Size" => Self::Size(),
            "NoPadding" => Self::NoPadding,
            "NonNull" => Self::NonNull,
            "Allocated" => {
                Self::check_arg_length(exprs.len(), 3, "Allocated");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Allocated");
                let length = Self::parse_length(tcx, def_id, &exprs[2], "Allocated");
                Self::Allocated(ty, length)
            }
            "InBound" => {
                Self::check_arg_length(exprs.len(), 3, "InBound");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "InBound");
                let length = Self::parse_length(tcx, def_id, &exprs[2], "InBound");
                Self::InBound(ty, length)
            }
            "NonOverlap" => Self::NonOverlap,
            "ValidNum" => {
                Self::check_arg_length(exprs.len(), 1, "ValidNum");
                let bin_op = BinOp::Ne;
                let length = Self::parse_length(tcx, def_id, &exprs[0], "ValidNum");
                return Self::ValidNum(CisRange::new(bin_op, length));
            }
            "ValidString" => Self::ValidString,
            "ValidCStr" => Self::ValidCStr,
            "Init" => {
                Self::check_arg_length(exprs.len(), 3, "Init");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Init");
                let length = Self::parse_length(tcx, def_id, &exprs[2], "Init");
                Self::Init(ty, length)
            }
            "Unwrap" => Self::Unwrap,
            "Typed" => {
                Self::check_arg_length(exprs.len(), 2, "Typed");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Typed");
                Self::Typed(ty)
            }
            "Owning" => Self::Owning,
            "Alias" => Self::Alias,
            "Alive" => Self::Alive,
            "Pinned" => Self::Pinned,
            "NonVolatile" => Self::NonVolatile,
            "Opened" => Self::Opened,
            "Trait" => Self::Trait,
            "Unreachable" => Self::Unreachable,
            "ValidPtr" => {
                Self::check_arg_length(exprs.len(), 3, "ValidPtr");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "ValidPtr");
                let length = Self::parse_length(tcx, def_id, &exprs[2], "ValidPtr");
                Self::ValidPtr(ty, length)
            }
            "Deref" => Self::Deref,
            "Ptr2Ref" => Self::Ptr2Ref,
            "Layout" => Self::Layout,
            _ => Self::Unknown,
        }
    }

    pub fn new_patial_order(p: usize, op: BinOp) -> Self {
        Self::ValidNum(CisRange::new(op, CisRangeItem::Var(p, Vec::new())))
    }

    pub fn new_obj_boundary(ty: Ty<'tcx>, len: CisRangeItem) -> Self {
        Self::InBound(ty, len)
    }

    // -------- length checker ----------
    fn check_arg_length(expr_len: usize, required_len: usize, sp: &str) -> bool {
        if expr_len != required_len {
            panic!("Wrong args length for {:?} Tag!", sp);
        }
        true
    }

    // -------- type parser ----------
    fn parse_type(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr, sp: &str) -> Ty<'tcx> {
        let ty_ident_full = access_ident_recursive(expr);
        if ty_ident_full.is_none() {
            rap_error!("Incorrect expression for the type of {:?} Tag!", sp);
        }
        let ty_ident = ty_ident_full.unwrap().0;
        let ty = match_ty_with_ident(tcx, def_id, ty_ident);
        if ty.is_none() {
            rap_error!("Cannot get type in {:?} Tag!", sp);
        }
        return ty.unwrap();
    }

    // -------- cis range parser ----------
    fn parse_length(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr, sp: &str) -> CisRangeItem {
        if let Some(var_len) = parse_expr_into_local_and_ty(tcx, def_id, expr) {
            CisRangeItem::Var(var_len.0, var_len.1.iter().map(|(x, _)| *x).collect())
        } else if parse_expr_into_number(expr).is_some() {
            CisRangeItem::Value(parse_expr_into_number(expr).unwrap())
        } else {
            rap_error!("Range length error in {:?} Tag!", sp);
            CisRangeItem::Unknown
        }
    }
}

#[derive(Debug, Clone)]
pub struct ContractualInvariantState<'tcx> {
    pub contracts: Vec<PropertyContract<'tcx>>,
}

impl<'tcx> ContractualInvariantState<'tcx> {
    pub fn new_default() -> Self {
        Self {
            contracts: Vec::new(),
        }
    }

    pub fn add_contract(&mut self, contract: PropertyContract<'tcx>) {
        self.contracts.push(contract);
    }

    pub fn get_contracts_length(&self) -> usize {
        self.contracts.len()
    }
}
