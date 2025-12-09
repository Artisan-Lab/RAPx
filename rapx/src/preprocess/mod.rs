pub mod dummy_fns;
pub mod ssa_preprocess;

use rustc_ast::{token::CommentKind, *};
use rustc_span::{DUMMY_SP, symbol::Symbol};

/// Empty `#[doc]` on the struct.
/// cc https://github.com/Artisan-Lab/RAPx/issues/184
pub fn doc_attr() -> Attribute {
    Attribute {
        kind: AttrKind::DocComment(CommentKind::Line, Symbol::intern("doc")),
        id: AttrId::ZERO,
        style: AttrStyle::Outer,
        span: DUMMY_SP,
    }
}
