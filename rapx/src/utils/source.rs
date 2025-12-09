use rustc_hir::{self, Node::*};
use rustc_middle::ty::TyCtxt;
use rustc_span::{
    FileName, FileNameDisplayPreference,
    def_id::{CrateNum, DefId},
    symbol::Symbol,
};
/*
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
*/
pub fn get_crate_num<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> Option<CrateNum> {
    let sym = Symbol::intern(name);
    tcx.crates(())
        .iter()
        .cloned()
        .find(|&cnum| tcx.crate_name(cnum) == sym)
}

pub fn get_fn_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    let name = tcx.def_path(def_id).to_string_no_crate_verbose();
    Some(name)
}

pub fn get_fn_name_byid(def_id: &DefId) -> String {
    let s = format!("{:?}", *def_id);
    if let Some(start) = s.find("DefId") {
        if let Some(end) = s.find("]::") {
            let s1 = s.replace(&s[start..end + 3], "").to_string();
            if let Some(start) = s1.find(")") {
                let result = s1.replace(&s1[start..start + 1], "").to_string();
                return result;
            }
            return s1;
        }
    }
    s.clone()
}
pub fn get_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<Symbol> {
    if def_id.is_local() {
        if let Some(node) = tcx.hir_get_if_local(def_id) {
            match node {
                Item(item) => {
                    let ident = tcx.hir_ident(item.hir_id());
                    return Some(ident.name);
                }
                ImplItem(item) => {
                    let ident = tcx.hir_ident(item.hir_id());
                    return Some(ident.name);
                }
                ForeignItem(item) => {
                    let ident = tcx.hir_ident(item.hir_id());
                    return Some(ident.name);
                }
                TraitItem(item) => {
                    let ident = tcx.hir_ident(item.hir_id());
                    return Some(ident.name);
                }
                _ => {
                    return None;
                }
            }
        }
    }
    None
}

pub fn get_filename(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    // Get the HIR node corresponding to the DefId
    if let Some(local_id) = def_id.as_local() {
        let hir_id = tcx.local_def_id_to_hir_id(local_id);
        let span = tcx.hir_span(hir_id);
        let source_map = tcx.sess.source_map();

        // Retrieve the file name
        if let Some(filename) = source_map.span_to_filename(span).into() {
            return Some(convert_filename(filename));
        }
    }
    None
}

fn convert_filename(filename: FileName) -> String {
    match filename {
        FileName::Real(path) => path
            .to_string_lossy(FileNameDisplayPreference::Local)
            .into_owned(),
        _ => "<unknown>".to_string(),
    }
}

pub fn get_module_name(tcx: TyCtxt, def_id: DefId) -> String {
    let tcx = tcx;
    let parent_mod = tcx.parent_module_from_def_id(def_id.expect_local());
    let mod_def_id = parent_mod.to_def_id();

    let path = tcx.def_path_str(mod_def_id);
    if path.is_empty() {
        "root_module".to_string()
    } else {
        path
    }
}
