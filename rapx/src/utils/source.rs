use rustc_hir::Node::*;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_span::symbol::Symbol;
use rustc_span::{FileName, FileNameDisplayPreference};

extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

pub fn get_fn_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    let name = tcx.def_path(def_id).to_string_no_crate_verbose();
    Some(name)
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
