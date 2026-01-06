use rustc_middle::ty::{self, Ty, TyCtxt};

#[derive(PartialEq, Debug, Copy, Clone)]
/// Represents different kinds of types for alias analysis purposes.
/// This is a wrapper of rustc_middle::ty, except that treat some types as corner cases;
pub enum TyKind {
    /// Algebraic Data Type (structs, enums, basic composite types).
    Adt,
    /// Raw pointer type, e.g., `*const T` or `*mut T`.
    RawPtr,
    /// Reference type, e.g., `&T` or `&mut T`.
    Ref,
    /// Tuple type, e.g., `(T1, T2, ...)`.
    Tuple,
    /// Special cases such as `RefCell`, `Rc`, etc., which need to be treated differently.
    CornerCase,
}

/// Analyzes a `Ty` (Rustc type) and returns its `TyKind` for alias analysis.
///
/// This function inspects the Rustc type and categorizes it into one of the `TyKind` variants.
/// Special types such as `RefCell`, `RefMut`, and `Rc` are further mapped to `CornerCase`.
///
/// # Arguments
/// * `ty` - The type to be classified.
///
/// # Returns
/// * `TyKind` - The classified type kind.
pub fn kind(ty: Ty<'_>) -> TyKind {
    match ty.kind() {
        ty::RawPtr(..) => TyKind::RawPtr,
        ty::Ref(..) => TyKind::Ref,
        ty::Tuple(..) => TyKind::Tuple,
        ty::Adt(adt, _) => {
            // Use string matching to catch RefCell/RefMut/Rc for special handling.
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

/// Determines whether a given type will never need drop (i.e., is trivially copyable and has no destructor).
///
/// Recursively checks all fields of aggregate types (tuples/structs/arrays) to ensure none require drop.
/// Used for optimization in alias analysis or memory management.
///
/// # Arguments
/// * `tcx` - The type context from rustc.
/// * `ty` - The type to check.
///
/// # Returns
/// * `true` if the type and all its components are trivially "not drop", `false` otherwise.
pub fn is_not_drop<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        // Primitive types that never require drop.
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => true,
        // For arrays, check element type.
        ty::Array(tys, _) => is_not_drop(tcx, *tys),
        // For ADTs (structs, enums), check all fields.
        ty::Adt(adtdef, substs) => {
            for field in adtdef.all_fields() {
                if !is_not_drop(tcx, field.ty(tcx, substs)) {
                    return false;
                }
            }
            true
        }
        // For tuples, check each element recursively.
        ty::Tuple(tuple_fields) => {
            for tys in tuple_fields.iter() {
                if !is_not_drop(tcx, tys) {
                    return false;
                }
            }
            true
        }
        // All other types may require drop.
        _ => false,
    }
}
