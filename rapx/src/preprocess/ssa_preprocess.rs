use rustc_ast::ast::{self, Item, ItemKind, VariantData};
use rustc_ast::ptr::P;
use rustc_ast::FieldDef;
use rustc_span::symbol::Ident;
use rustc_span::symbol::Symbol;
use rustc_span::DUMMY_SP;
use thin_vec::ThinVec;

use crate::rap_debug;
pub(crate) fn create_ssa_struct(_krate: &mut ast::Crate) {
    rap_debug!("[CALLBACK] Injecting new structs into the AST...");

    let ssa_struct = create_struct(
        "SSAstmt",
        vec![
            ("para1", Symbol::intern("i128")),
            ("para2", Symbol::intern("i128")),
            ("para3", Symbol::intern("i128")),
            ("para4", Symbol::intern("i128")),
            ("para5", Symbol::intern("i128")),
            ("para6", Symbol::intern("i128")),
            ("para7", Symbol::intern("i128")),
            ("para8", Symbol::intern("i128")),
            ("para9", Symbol::intern("i128")),
            ("para10", Symbol::intern("i128")),
        ],
    );

    let essa_struct = create_struct(
        "ESSAstmt",
        vec![
            ("op1", Symbol::intern("i128")),
            ("op2", Symbol::intern("i128")),
            ("cmp", Symbol::intern("i128")),
        ],
    );

    _krate.items.push(ssa_struct);
    _krate.items.push(essa_struct);

    // println!("[CALLBACK] Injection complete. Continuing compilation...");
}
pub(crate) fn create_struct(name: &str, fields_def: Vec<(&str, Symbol)>) -> P<Item> {
    let fields: ThinVec<FieldDef> = fields_def
        .into_iter()
        .map(|(fname, fty)| ast::FieldDef {
            attrs: vec![].into(),
            vis: ast::Visibility {
                span: DUMMY_SP,
                kind: ast::VisibilityKind::Public,
                tokens: None,
            },
            ident: Some(Ident::from_str(fname)),
            ty: P(ast::Ty {
                id: ast::NodeId::from_u32(0),
                kind: ast::TyKind::Path(None, ast::Path::from_ident(Ident::with_dummy_span(fty))),
                span: DUMMY_SP,
                tokens: None,
            }),
            id: ast::NodeId::from_u32(0),
            span: DUMMY_SP,
            is_placeholder: false,
            safety: ast::Safety::Default,
            default: None,
        })
        .collect();

    let ident = Ident {
        name: Symbol::intern(name),
        span: DUMMY_SP,
    };
    let variant_data = VariantData::Struct {
        fields: fields,
        recovered: rustc_ast::Recovered::No,
    };

    let item_kind = ItemKind::Struct(ident, ast::Generics::default(), variant_data);

    P(Item {
        attrs: vec![].into(),
        id: ast::NodeId::from_u32(0),
        kind: item_kind,
        vis: ast::Visibility {
            span: DUMMY_SP,
            kind: ast::VisibilityKind::Public,
            tokens: None,
        },
        span: DUMMY_SP,
        tokens: None,
    })
}
