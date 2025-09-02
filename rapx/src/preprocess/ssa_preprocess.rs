use rustc_ast::{token::CommentKind, *};
use rustc_span::{
    symbol::{Ident, Symbol},
    DUMMY_SP,
};
use thin_vec::ThinVec;

use crate::rap_debug;
pub(crate) fn create_ssa_struct(_krate: &mut Crate) {
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
pub(crate) fn create_struct(name: &str, fields_def: Vec<(&str, Symbol)>) -> Box<Item> {
    let fields: ThinVec<FieldDef> = fields_def
        .into_iter()
        .map(|(fname, fty)| FieldDef {
            attrs: ThinVec::from([doc_attr()]),
            vis: Visibility {
                span: DUMMY_SP,
                kind: VisibilityKind::Public,
                tokens: None,
            },
            ident: Some(Ident::from_str(fname)),
            ty: Box::new(Ty {
                id: NodeId::from_u32(0),
                kind: TyKind::Path(None, Path::from_ident(Ident::with_dummy_span(fty))),
                span: DUMMY_SP,
                tokens: None,
            }),
            id: NodeId::from_u32(0),
            span: DUMMY_SP,
            is_placeholder: false,
            safety: Safety::Default,
            default: None,
        })
        .collect();

    let ident = Ident {
        name: Symbol::intern(name),
        span: DUMMY_SP,
    };
    let variant_data = VariantData::Struct {
        fields,
        recovered: Recovered::No,
    };

    let item_kind = ItemKind::Struct(ident, Generics::default(), variant_data);

    Box::new(Item {
        attrs: ThinVec::from([doc_attr()]),
        id: NodeId::from_u32(0),
        kind: item_kind,
        vis: Visibility {
            span: DUMMY_SP,
            kind: VisibilityKind::Public,
            tokens: None,
        },
        span: DUMMY_SP,
        tokens: None,
    })
}

/// Empty `#[doc]` on the struct.
/// cc https://github.com/Artisan-Lab/RAPx/issues/184
fn doc_attr() -> Attribute {
    Attribute {
        kind: AttrKind::DocComment(CommentKind::Line, Symbol::intern("doc")),
        id: AttrId::ZERO,
        style: AttrStyle::Outer,
        span: DUMMY_SP,
    }
}
