use crate::{
    analysis::utils::fn_info::{
        access_ident_recursive, match_ty_with_ident, parse_expr_into_local_and_ty,
        parse_expr_into_number,
    },
    rap_error,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Ty;
use rustc_middle::ty::TyCtxt;
use safety_parser::{
    property_attr::property::{Kind, PropertyName},
    syn::Expr,
};

#[derive(Clone, Debug)]
pub enum MemLen {
    Var(usize, Vec<usize>),
    Value(usize),
    Unknown,
}

#[derive(Clone, Debug)]
pub enum PropertyContract<'tcx> {
    // Align (ty)
    Align(Ty<'tcx>),
    Size(Kind),
    NoPadding,
    NonNull,
    // Allocated( ty, length)
    Allocated(Ty<'tcx>, MemLen),
    // InBound( ty, length)
    InBound(Ty<'tcx>, MemLen),
    NonOverlap,
    ValidNum,
    ValidString,
    ValidCStr,
    // Init( ty, length)
    Init(Ty<'tcx>, MemLen),
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
    ValidPtr(Ty<'tcx>, MemLen),
    Deref,
    Ptr2Ref,
    Layout,
    Unknown,
}

impl<'tcx> PropertyContract<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        kind: Kind,
        name: PropertyName,
        exprs: &Vec<Expr>,
    ) -> Self {
        match name {
            PropertyName::Align => {
                if exprs.len() <= 1 {
                    rap_error!("Wrong args length for Align Tag!");
                }
                let ty_ident_full = access_ident_recursive(&exprs[1]);
                if ty_ident_full.is_none() {
                    rap_error!("Incorrect expression for the type of Align Tag!");
                }
                let ty_ident = ty_ident_full.unwrap().0;
                let ty = match_ty_with_ident(tcx, def_id, ty_ident);
                if ty.is_none() {
                    rap_error!("Cannot get type in Align Tag!");
                }
                Self::Align(ty.unwrap())
            }
            PropertyName::Size => Self::Size(kind),
            PropertyName::NoPadding => Self::NoPadding,
            PropertyName::NonNull => Self::NonNull,
            PropertyName::Allocated => {
                if exprs.len() <= 2 {
                    rap_error!("Wrong args length for Allocated Tag!");
                }
                let ty_ident_full = access_ident_recursive(&exprs[1]);
                if ty_ident_full.is_none() {
                    rap_error!("Incorrect expression for the type of Allocated Tag!");
                }
                let ty_ident = ty_ident_full.unwrap().0;
                let ty = match_ty_with_ident(tcx, def_id, ty_ident);
                if ty.is_none() {
                    rap_error!("Cannot get type in Allocated Tag!");
                }
                let length = {
                    if let Some(var_len) =
                        parse_expr_into_local_and_ty(tcx, def_id, exprs[2].clone())
                    {
                        MemLen::Var(var_len.0, var_len.1)
                    } else if parse_expr_into_number(&exprs[2]).is_some() {
                        MemLen::Value(1)
                    } else {
                        rap_error!("Length error in Allocated Tag!");
                        MemLen::Unknown
                    }
                };
                Self::Allocated(ty.unwrap(), length)
            }
            PropertyName::InBound => {
                if exprs.len() <= 2 {
                    rap_error!("Wrong args length for InBound Tag!");
                }
                let ty_ident_full = access_ident_recursive(&exprs[1]);
                if ty_ident_full.is_none() {
                    rap_error!("Incorrect expression for the type of InBound Tag!");
                }
                let ty_ident = ty_ident_full.unwrap().0;
                let ty = match_ty_with_ident(tcx, def_id, ty_ident);
                if ty.is_none() {
                    rap_error!("Cannot get type in InBound Tag!");
                }
                let length = {
                    if let Some(var_len) =
                        parse_expr_into_local_and_ty(tcx, def_id, exprs[2].clone())
                    {
                        MemLen::Var(var_len.0, var_len.1)
                    } else if parse_expr_into_number(&exprs[2]).is_some() {
                        MemLen::Value(1)
                    } else {
                        rap_error!("Length error in InBound Tag!");
                        MemLen::Unknown
                    }
                };
                Self::InBound(ty.unwrap(), length)
            }
            PropertyName::NonOverlap => Self::NonOverlap,
            PropertyName::ValidNum => Self::ValidNum,
            PropertyName::ValidString => Self::ValidString,
            PropertyName::ValidCStr => Self::ValidCStr,
            PropertyName::Init => {
                if exprs.len() <= 2 {
                    rap_error!("Wrong args length for Init Tag!");
                }
                let ty_ident_full = access_ident_recursive(&exprs[1]);
                if ty_ident_full.is_none() {
                    rap_error!("Incorrect expression for the type of Init Tag!");
                }
                let ty_ident = ty_ident_full.unwrap().0;
                let ty = match_ty_with_ident(tcx, def_id, ty_ident);
                if ty.is_none() {
                    rap_error!("Cannot get type in Init Tag!");
                }
                let length = {
                    if let Some(var_len) =
                        parse_expr_into_local_and_ty(tcx, def_id, exprs[2].clone())
                    {
                        MemLen::Var(var_len.0, var_len.1)
                    } else if parse_expr_into_number(&exprs[2]).is_some() {
                        MemLen::Value(1)
                    } else {
                        rap_error!("Length error in Init Tag!");
                        MemLen::Unknown
                    }
                };
                Self::Init(ty.unwrap(), length)
            }
            PropertyName::Unwrap => Self::Unwrap,
            PropertyName::Typed => {
                if exprs.len() <= 1 {
                    rap_error!("Wrong args length for Typed Tag!");
                }
                let ty_ident_full = access_ident_recursive(&exprs[1]);
                if ty_ident_full.is_none() {
                    rap_error!("Incorrect expression for the type of Typed Tag!");
                }
                let ty_ident = ty_ident_full.unwrap().0;
                let ty = match_ty_with_ident(tcx, def_id, ty_ident);
                if ty.is_none() {
                    rap_error!("Cannot get type in Typed Tag!");
                }
                Self::Typed(ty.unwrap())
            }
            PropertyName::Owning => Self::Owning,
            PropertyName::Alias => Self::Alias,
            PropertyName::Alive => Self::Alive,
            PropertyName::Pinned => Self::Pinned,
            PropertyName::NonVolatile => Self::NonVolatile,
            PropertyName::Opened => Self::Opened,
            PropertyName::Trait => Self::Trait,
            PropertyName::Unreachable => Self::Unreachable,
            PropertyName::ValidPtr => {
                if exprs.len() <= 2 {
                    rap_error!("Wrong args length for ValidPtr Tag!");
                }
                let ty_ident_full = access_ident_recursive(&exprs[1]);
                if ty_ident_full.is_none() {
                    rap_error!("Incorrect expression for the type of ValidPtr Tag!");
                }
                let ty_ident = ty_ident_full.unwrap().0;
                let ty = match_ty_with_ident(tcx, def_id, ty_ident);
                if ty.is_none() {
                    rap_error!("Cannot get type in ValidPtr Tag!");
                }
                let length = {
                    if let Some(var_len) =
                        parse_expr_into_local_and_ty(tcx, def_id, exprs[2].clone())
                    {
                        MemLen::Var(var_len.0, var_len.1)
                    } else if parse_expr_into_number(&exprs[2]).is_some() {
                        MemLen::Value(1)
                    } else {
                        rap_error!("Length error in ValidPtr Tag!");
                        MemLen::Unknown
                    }
                };
                Self::ValidPtr(ty.unwrap(), length)
            }
            PropertyName::Deref => Self::Deref,
            PropertyName::Ptr2Ref => Self::Ptr2Ref,
            PropertyName::Layout => Self::Layout,
            PropertyName::Unknown => Self::Unknown,
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
