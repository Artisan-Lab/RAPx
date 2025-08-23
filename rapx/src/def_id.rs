extern crate indexmap;
extern crate rustc_public;

// use crate::rap_info;
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{rustc_internal, CrateDef};
use std::sync::OnceLock;

static INIT: OnceLock<Intrinsics> = OnceLock::new();

struct Intrinsics {
    map: IndexMap<&'static str, DefId>,
}

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| {
        rustc_internal::run(tcx, || init_inner(tcx)).expect("Failed to run rustc_public.")
    });
}

fn init_inner(tcx: TyCtxt) -> Intrinsics {
    const CRATES: &[&str] = &["core", "std", "alloc"];

    let mut map = IndexMap::with_capacity(INTRINSICS.len());
    for krate in rustc_public::external_crates() {
        if !CRATES.iter().any(|name| *name == krate.name) {
            continue;
        }
        for fn_def in krate.fn_defs() {
            let fn_name = fn_def.name();
            if let Some(name) = INTRINSICS
                .iter()
                .find_map(|&name| (name == fn_name).then_some(name))
            {
                // if INTRINSICS.iter().any(|name| fn_name.contains(name)) {
                let def_id = rustc_internal::internal(tcx, fn_def.def_id());
                if map.contains_key(name) {
                    panic!("DefId of {fn_name} has been inserted: {def_id:?}");
                } else {
                    map.insert(name, def_id);
                }
            }
        }
    }

    map.sort_unstable_by(|a, _, b, _| a.cmp(b));
    assert_eq!(
        INTRINSICS.len(),
        map.len(),
        "Intrinsic functions is incompletely retrieved.\n\
         INTRINSICS = {INTRINSICS:#?}\nmap ={map:#?}"
    );
    // rap_info!("Intrinsic = {map:#?}");
    Intrinsics { map }
}

macro_rules! intrinsics {
    ($( $id:ident : $call:literal ,)+ ) => {
        const INTRINSICS: &[&str] = &[$($call,)+];
        $(
            pub fn $id() -> DefId {
                *INIT.get().expect("Intrinsics DefIds haven't been initialized.").map.get($call)
                    .unwrap_or_else(|| panic!("Failed to retrieve the DefId of {}.", $call))
            }
        )+
    };
}

intrinsics! {
    assume_init_drop: "std::mem::MaybeUninit::<T>::assume_init_drop",
    call_mut: "std::ops::FnMut::call_mut",
    clone: "std::clone::Clone::clone",
    copy_from: "std::ptr::mut_ptr::<impl *mut T>::copy_from",
    copy_from_nonoverlapping: "std::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping",
    copy_to: "std::ptr::const_ptr::<impl *const T>::copy_to",
    copy_to_nonoverlapping: "std::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping",
    dealloc: "std::alloc::dealloc",
    drop: "std::mem::drop",
    drop_in_place: "std::ptr::drop_in_place",
    manually_drop: "std::mem::ManuallyDrop::<T>::drop",
}
