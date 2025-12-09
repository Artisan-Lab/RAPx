extern crate indexmap;

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use std::sync::OnceLock;

static INIT: OnceLock<Intrinsics> = OnceLock::new();

struct Intrinsics {
    // The key is fn path, starting from `core::` or `std::`. The value is internal def id.
    map: IndexMap<Box<str>, DefId>,
}

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| init_inner(tcx));
}

fn init_inner(tcx: TyCtxt) -> Intrinsics {
    const CRATES: &[&str] = &["core", "std", "alloc"];

    // The key is an index to INTRINSICS slice; the value means if the path is found.
    let mut indices: IndexMap<_, _> = (0..INTRINSICS.len()).map(|idx| (idx, false)).collect();

    let mut map = IndexMap::<Box<str>, DefId>::with_capacity(INTRINSICS.len());
    for krate in rustc_public::external_crates() {
        if !CRATES.iter().any(|name| *name == krate.name) {
            continue;
        }

        for fn_def in krate.fn_defs() {
            let fn_name = fn_def.name();
            if let Some(name) = INTRINSICS.iter().enumerate().find_map(|(idx, paths)| {
                if paths.iter().any(|path| **path == fn_name) {
                    assert_eq!(
                        indices.insert(idx, true),
                        Some(false),
                        "DefId for {fn_name} has been found: {:?}",
                        map.get(&*fn_name)
                    );
                    Some(fn_name.as_str().into())
                } else {
                    None
                }
            }) {
                let def_id = rustc_internal::internal(tcx, fn_def.def_id());
                if map.contains_key(&name) {
                    panic!("DefId of {fn_name} has been inserted: {def_id:?}");
                } else {
                    map.insert(name, def_id);
                }
            }
        }
    }

    map.sort_unstable_by(|a, _, b, _| a.cmp(b));

    if INTRINSICS.len() != map.len() {
        // The reason to not make this an assertion is allowing compilation on
        // missing instrinsics, e.g. no_std crates without using alloc will never
        // have the dealloc intrinsic.
        // cc https://github.com/Artisan-Lab/RAPx/issues/190#issuecomment-3303049000
        let not_found = indices
            .iter()
            .filter_map(|(&idx, &found)| (!found).then_some(INTRINSICS[idx]))
            .collect::<Vec<_>>();
        rap_warn!(
            "Intrinsic functions is incompletely retrieved.\n\
             {} fn ids are not found: {not_found:#?}",
            not_found.len()
        );
    }

    Intrinsics { map }
}

macro_rules! intrinsics {
    ($( $id:ident : $paths:expr ,)+ ) => {
        const INTRINSICS: &[&[&str]] = &[$( $paths ,)+];
        $(
            pub fn $id() -> DefId {
                ${concat($id, _opt)} ().unwrap_or_else(||
                    panic!("Failed to retrieve the DefId of {:#?}.", $paths)
                )
            }

            pub fn ${concat($id, _opt)} () -> Option<DefId> {
                let map = &INIT.get().expect("Intrinsics DefIds haven't been initialized.").map;
                for path in $paths {
                    match map.get(*path) {
                        Some(id) => return Some(*id),
                        None => ()
                    }
                }
                None
            }
        )+
    };
}

// for #![no_std] crates, intrinsics fn paths start from core instead of core.
// cc https://github.com/Artisan-Lab/RAPx/issues/190
intrinsics! {
    assume_init_drop: &[
        "std::mem::MaybeUninit::<T>::assume_init_drop",
        "core::mem::MaybeUninit::<T>::assume_init_drop"
    ],
    call_mut: &[
        "std::ops::FnMut::call_mut",
        "core::ops::FnMut::call_mut"
    ],
    clone: &[
        "std::clone::Clone::clone",
        "core::clone::Clone::clone"
    ],
    copy_from: &[
        "std::ptr::mut_ptr::<impl *mut T>::copy_from",
        "core::ptr::mut_ptr::<impl *mut T>::copy_from"
    ],
    copy_from_nonoverlapping: &[
        "std::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping",
        "core::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping"
    ],
    copy_to: &[
        "std::ptr::const_ptr::<impl *const T>::copy_to",
        "core::ptr::const_ptr::<impl *const T>::copy_to",
    ],
    copy_to_nonoverlapping: &[
        "std::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping",
        "core::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping"
    ],
    dealloc: &[
        "std::alloc::dealloc",
        "alloc::alloc::dealloc"
    ],
    drop: &[
        "std::mem::drop",
        "core::mem::drop",
    ],
    drop_in_place: &[
        "std::ptr::drop_in_place",
        "core::ptr::drop_in_place",
    ],
    manually_drop: &[
        "std::mem::ManuallyDrop::<T>::drop",
        "core::mem::ManuallyDrop::<T>::drop"
    ],
}

/// rustc_public DefId to internal DefId
pub fn to_internal<T: CrateDef>(val: &T, tcx: TyCtxt) -> DefId {
    rustc_internal::internal(tcx, val.def_id())
}
