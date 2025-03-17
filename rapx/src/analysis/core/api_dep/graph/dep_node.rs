use std::hash::Hash;

use super::ty_wrapper::TyWrapper;
use rustc_middle::{
    query::IntoQueryParam,
    ty::{Ty, TyCtxt},
};

use rustc_hir::def_id::DefId;

#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
enum IntrinsicKind {
    Borrow,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum DepNode<'tcx> {
    Api(DefId),
    Ty(TyWrapper<'tcx>),
    GenericParamDef(DefId, usize, String, bool), // (fn_def_id, index, symbol, is_lifetime_param)
}

pub fn desc_str<'tcx>(node: DepNode<'tcx>, tcx: TyCtxt<'tcx>) -> String {
    match node {
        DepNode::Api(def_id) => tcx.def_path_str(def_id),
        DepNode::Ty(ty) => ty.desc_str(tcx),
        DepNode::GenericParamDef(idx, index, sym, is_lifetime) => {
            format!("{sym}/#{index}")
        }
    }
}

impl<'tcx> DepNode<'tcx> {
    pub fn api(id: impl IntoQueryParam<DefId>) -> DepNode<'tcx> {
        DepNode::Api(id.into_query_param())
    }
    pub fn ty(ty: Ty<'tcx>) -> DepNode<'tcx> {
        DepNode::Ty(TyWrapper::from(ty))
    }
    pub fn generic_param_def(
        fn_def_id: DefId,
        index: usize,
        name: impl ToString,
        is_lifetime: bool,
    ) -> DepNode<'tcx> {
        DepNode::GenericParamDef(fn_def_id, index, name.to_string(), is_lifetime)
    }
}
