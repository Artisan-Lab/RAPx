use rustc_data_structures::fx::FxHashMap;
use rustc_hir::ImplItemKind;
use rustc_hir::{
    def_id::DefId, intravisit, intravisit::Visitor, Block, Body, BodyId, ExprKind, HirId, Impl,
    ItemKind, QPath,
};
use rustc_middle::hir::nested_filter;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::Span;
use std::collections::HashSet;

/// Maps `HirId` of a type to `BodyId` of related impls.
pub type RelatedItemMap = FxHashMap<Option<HirId>, Vec<(BodyId, Span)>>;

pub struct RelatedFnCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    hash_map: RelatedItemMap,
}

impl<'tcx> RelatedFnCollector<'tcx> {
    pub fn collect(tcx: TyCtxt<'tcx>) -> RelatedItemMap {
        let mut collector = RelatedFnCollector {
            tcx,
            hash_map: RelatedItemMap::default(),
        };

        tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        collector.hash_map
    }
}

impl<'tcx> Visitor<'tcx> for RelatedFnCollector<'tcx> {
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        match &item.kind {
            ItemKind::Impl(Impl {
                generics: _generics,
                self_ty,
                items: impl_items,
                ..
            }) => {
                let key = Some(self_ty.hir_id);
                let entry = self.hash_map.entry(key).or_default();
                entry.extend(impl_items.iter().filter_map(|impl_item_ref| {
                    if let rustc_hir::AssocItemKind::Fn { has_self: _ } = impl_item_ref.kind {
                        let hir_id = impl_item_ref.id.hir_id();
                        self.tcx
                            .hir_maybe_body_owned_by(hir_id.owner.def_id)
                            .map(|body| (body.id(), impl_item_ref.span))
                    } else {
                        None
                    }
                }));
            }
            ItemKind::Trait(_is_auto, _safety, _ident, _generics, _generic_bounds, trait_items) => {
                let key = None;
                let entry = self.hash_map.entry(key).or_default();
                entry.extend(trait_items.iter().filter_map(|trait_item_ref| {
                    if let rustc_hir::AssocItemKind::Fn { has_self: _ } = trait_item_ref.kind {
                        let hir_id = trait_item_ref.id.hir_id();
                        self.tcx
                            .hir_maybe_body_owned_by(hir_id.owner.def_id)
                            .map(|body| (body.id(), trait_item_ref.span))
                    } else {
                        None
                    }
                }));
            }
            ItemKind::Fn {
                sig: _,
                generics: _,
                body: body_id,
                has_body: _,
                ident,
            } => {
                let key = Some(body_id.hir_id);
                let entry = self.hash_map.entry(key).or_default();
                entry.push((*body_id, item.span));
            }
            _ => (),
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'tcx rustc_hir::TraitItem<'tcx>) {
        // We don't process items inside trait blocks
    }

    fn visit_impl_item(&mut self, _impl_item: &'tcx rustc_hir::ImplItem<'tcx>) {
        // We don't process items inside impl blocks
    }

    fn visit_foreign_item(&mut self, _foreign_item: &'tcx rustc_hir::ForeignItem<'tcx>) {
        // We don't process foreign items
    }
}

pub struct ContainsUnsafe<'tcx> {
    tcx: TyCtxt<'tcx>,
    function_unsafe: bool,
    block_unsafe: bool,
}

impl<'tcx> ContainsUnsafe<'tcx> {
    pub fn contains_unsafe(tcx: TyCtxt<'tcx>, body_id: BodyId) -> (bool, bool) {
        let mut visitor = ContainsUnsafe {
            tcx,
            function_unsafe: false,
            block_unsafe: false,
        };

        let body = visitor.tcx.hir_body(body_id);
        visitor.function_unsafe = visitor.body_unsafety(body);
        visitor.visit_body(body);

        (visitor.function_unsafe, visitor.block_unsafe)
    }

    fn body_unsafety(&self, body: &'tcx Body<'tcx>) -> bool {
        let did = body.value.hir_id.owner.to_def_id();
        let sig = self.tcx.fn_sig(did);
        if let rustc_hir::Safety::Unsafe = sig.skip_binder().safety() {
            return true;
        }
        false
    }
}

impl<'tcx> Visitor<'tcx> for ContainsUnsafe<'tcx> {
    // type NestedFilter = nested_filter::OnlyBodies;

    //fn nested_visit_map(&mut self) -> Self::Map {
    //    self.tcx.hir()
    //}

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        use rustc_hir::BlockCheckMode;
        if let BlockCheckMode::UnsafeBlock(_unsafe_source) = block.rules {
            // println!("{:?}",block.clone());
            self.block_unsafe = true;
        }
        intravisit::walk_block(self, block);
    }
}

pub struct ContainsLit {
    pub structs_used: HashSet<String>,
}

impl<'tcx> Visitor<'tcx> for ContainsLit {
    fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
        if let ExprKind::Struct(ref qpath, _, _) = expr.kind {
            if let QPath::Resolved(_, path) = qpath {
                if let Some(ident) = path.segments.last().map(|segment| segment.ident) {
                    self.structs_used.insert(ident.to_string());
                }
            }
        }
        intravisit::walk_expr(self, expr);
    }
}

/// (`DefId` of ADT) => Vec<(HirId of relevant impl block, impl_self_ty)>
/// We use this map to quickly access associated impl blocks per ADT.
/// `impl_self_ty` in the return value may differ from `tcx.type_of(ADT.DefID)`,
/// as different instantiations of the same ADT are distinct `Ty`s.
/// (e.g. Foo<i32, i64>, Foo<String, i32>)
pub type AdtImplMap<'tcx> = FxHashMap<DefId, Vec<(DefId, Ty<'tcx>)>>;

/// Create & initialize `AdtImplMap`.
/// `AdtImplMap` is initialized before analysis of each crate,
/// avoiding quadratic complexity of scanning all impl blocks for each ADT.
pub fn create_adt_impl_map(tcx: TyCtxt<'_>) -> AdtImplMap<'_> {
    let mut map = FxHashMap::default();
    for impl_item_id in tcx.hir_crate_items(()).impl_items() {
        let impl_item = tcx.hir_impl_item(impl_item_id);
        match impl_item.kind {
            ImplItemKind::Type(ty) => {
                let impl_self_ty = tcx.type_of(ty.hir_id.owner).skip_binder();
                if let ty::Adt(impl_self_adt_def, _impl_substs) = impl_self_ty.kind() {
                    map.entry(impl_self_adt_def.did())
                        .or_insert_with(Vec::new)
                        .push((impl_item_id.owner_id.to_def_id(), impl_self_ty));
                }
            }
            _ => (),
        }
    }
    map
}
