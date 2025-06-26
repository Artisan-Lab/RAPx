use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt};

#[derive(PartialEq, Debug, Copy, Clone)]
pub enum TyKind {
    Adt,
    RawPtr,
    Tuple,
    CornerCase,
    Ref,
}

pub fn kind(current_ty: Ty<'_>) -> TyKind {
    match current_ty.kind() {
        ty::RawPtr(..) => TyKind::RawPtr,
        ty::Ref(..) => TyKind::Ref,
        ty::Tuple(..) => TyKind::Tuple,
        ty::Adt(ref adt, _) => {
            let s = format!("{:?}", adt);
            if s.contains("cell::RefMut") || s.contains("cell::Ref") || s.contains("rc::Rc") {
                TyKind::CornerCase
            } else {
                TyKind::Adt
            }
        }
        _ => TyKind::Adt,
    }
}

pub fn is_not_drop<'tcx>(tcx: TyCtxt<'tcx>, current_ty: Ty<'tcx>) -> bool {
    match current_ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
        ty::Array(ref tys, _) => is_not_drop(tcx, *tys),
        ty::Adt(ref adtdef, substs) => {
            for field in adtdef.all_fields() {
                if !is_not_drop(tcx, field.ty(tcx, substs)) {
                    return false;
                }
            }
            true
        }
        ty::Tuple(tuple_fields) => {
            for tys in tuple_fields.iter() {
                if !is_not_drop(tcx, tys) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}
