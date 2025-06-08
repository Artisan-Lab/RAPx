use rustc_abi::VariantIdx;
use rustc_middle::mir::visit::{TyContext, Visitor};
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, Body, Local, LocalDecl, Operand, TerminatorKind,
};
use rustc_middle::ty::EarlyBinder;
use rustc_middle::ty::{
    self, GenericArgKind, Ty, TyCtxt, TyKind, TypeSuperVisitable, TypeVisitable, TypeVisitor,
};
use rustc_span::def_id::DefId;

use std::collections::HashMap;
use std::ops::ControlFlow;

use super::*;
use crate::analysis::rcanary::RcxMut;
use crate::rap_debug;

// This function is aiming at resolving problems due to 'TyContext' not implementing 'Clone' trait,
// thus we call function 'copy_ty_context' to simulate 'self.clone()'.
#[inline(always)]
pub(crate) fn copy_ty_context(tc: &TyContext) -> TyContext {
    match tc {
        TyContext::LocalDecl { local, source_info } => TyContext::LocalDecl {
            local: local.clone(),
            source_info: source_info.clone(),
        },
        _ => unreachable!(),
    }
}

impl<'tcx, 'a> TypeAnalysis<'tcx, 'a> {
    // The 'visitor' method is our main pass of the constructor part in type analysis,
    // it will perform several important procedural to determine whether an adt definition (adt-def)
    // will occupy at least one heap allocation, reflecting holding heap-ownership in RAP system.
    //
    // From the top-down method of our approach, this 'visitor' is the set of several sub-phases
    // which means it contains multiple sub-visitors to make whole method 'self.visitor()' work.
    //
    // For example, given an adtef (like Vec<T>), the result of 'visitor' contains two parts:
    //
    //     pt1 Enum:  {Owned / UnOwned} indicates whether it will directly have a heap data
    //     pt2 Array: [bool;N] indicates whether each generic parameter will have a raw param
    //
    // Those 2 parts can accelerate heap-ownership inference in the data-flow analysis.
    pub fn visitor(&mut self) {
        #[inline(always)]
        fn start_channel<M>(mut method: M, v_did: &Vec<DefId>)
        where
            M: FnMut(DefId) -> (),
        {
            for did in v_did {
                method(*did);
            }
        }

        #[inline(always)]
        fn show_owner(ref_type_analysis: &mut TypeAnalysis) {
            for elem in ref_type_analysis.adt_owner() {
                let name = format!(
                    "{:?}",
                    EarlyBinder::skip_binder(ref_type_analysis.tcx().type_of(*elem.0))
                );
                let owning = format!("{:?}", elem.1);
                rap_debug!("ADT analysis: {} {}", name, owning);
            }
        }

        // Get the Global TyCtxt from rustc
        // Grasp all mir Keys defined in current crate
        let tcx = self.tcx();
        let mir_keys = tcx.mir_keys(());

        for each_mir in mir_keys {
            // Get the defid of current crate and get mir Body through this id
            let def_id = each_mir.to_def_id();
            let body = mir_body(tcx, def_id);

            // Insert the defid to hashset if is not existed and visit the body
            if self.fn_set_mut().insert(def_id) {
                self.visit_body(body);
            } else {
                continue;
            }
        }

        let dids: Vec<DefId> = self.adt_recorder.iter().map(|did| *did).collect();

        start_channel(|did| self.extract_raw_generic(did), &dids);
        start_channel(|did| self.extract_raw_generic_prop(did), &dids);
        start_channel(|did| self.extract_phantom_unit(did), &dids);
        start_channel(|did| self.extract_owner_prop(did), &dids);

        show_owner(self);
    }

    // Extract params in adt types, the 'param' means one generic parameter acting like 'T', 'A', etc...
    // In the sub-visitor RawGeneric, it will visit the given type recursively, and extract all params.
    //
    // Note that RAP is only interested in 'raw' params ('T' not like '*mut T').
    // It lies in 'one-entire field' | recursive in tuple | recursive in array | mixed before
    //
    // Given a struct Example<A, B, T, S>:
    //
    // struct Example<A, B, T, S> {
    //     a: A,
    //     b: (i32, (f64, B)),
    //     c: [[(S) ; 1] ; 2],
    //     d: Vec<T>,
    // }
    //
    // the final result for <A, B, T, S> is <true, true, false, true>.
    #[inline(always)]
    fn extract_raw_generic(&mut self, did: DefId) {
        // Get the definition and subset reference from adt did
        let ty = EarlyBinder::skip_binder(self.tcx().type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        let mut v_res = Vec::new();

        for variant in adt_def.variants().iter() {
            let mut raw_generic = IsolatedParam::new(substs.len());

            for field in &variant.fields {
                let field_ty = field.ty(self.tcx(), substs);
                field_ty.visit_with(&mut raw_generic);
            }
            v_res.push((RawTypeOwner::Unowned, raw_generic.record_mut().clone()));
        }

        self.adt_owner_mut().insert(did, v_res);
    }

    // Extract all params in the adt types like param 'T' and then propagate from the bottom to top.
    // This procedural is the successor of `extract_raw_generic`, and the main idea of RawGenericPropagation
    // is to propagate params from bottom adt to the top as well as updating TypeAnalysis Context.
    //
    // Note that it will thorough consider mono-morphization existed in adt-def.
    // That means the type 'Vec<T>', 'Vec<Vec<T>>' and 'Vec<i32>' are totally different!!!!
    //
    // Given a struct Example<A, B, T, S>:
    //
    // struct X<A> {
    //     a: A,
    // }
    // the final result for <A> is <true>.
    //
    // struct Y1<B> {
    //     a: (i32, (f64, B)),
    //     b: X<i32>,
    // }
    // the final result for <B> is <true>.
    //
    // struct Example<A, B, T, S> {
    //     a: X<A>,
    //     b: (i32, (f64, B)),
    //     c: [[(S) ; 1] ; 2],
    //     d: Vec<T>,
    // }
    //
    // the final result for <A, B, T, S> is <true, true, false, true>.
    #[inline(always)]
    fn extract_raw_generic_prop(&mut self, did: DefId) {
        // Get the definition and subset reference from adt did
        let ty = EarlyBinder::skip_binder(self.tcx().type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        let source_enum = adt_def.is_enum();

        let mut v_res = self.adt_owner_mut().get_mut(&did).unwrap().clone();

        for (variant_index, variant) in adt_def.variants().iter().enumerate() {
            let res = v_res[variant_index as usize].clone();

            let mut raw_generic_prop = IsolatedParamPropagation::new(
                self.tcx(),
                res.1.clone(),
                source_enum,
                self.adt_owner(),
            );

            for field in &variant.fields {
                let field_ty = field.ty(self.tcx(), substs);
                field_ty.visit_with(&mut raw_generic_prop);
            }
            v_res[variant_index as usize] =
                (RawTypeOwner::Unowned, raw_generic_prop.record_mut().clone());
        }

        self.adt_owner_mut().insert(did, v_res);
    }

    // Extract all types that include PhantomData<T> which T must be a raw Param
    // Consider these types as a unit to guide the traversal over adt types
    #[inline(always)]
    fn extract_phantom_unit(&mut self, did: DefId) {
        // Get ty from defid and the ty is made up with generic type
        let ty = EarlyBinder::skip_binder(self.tcx().type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        // As for one heap-allocation unit, only struct will contains the information that we want
        // Example:
        // struct Foo<T> {
        //     NonNull<T>,      // this indicates a pointer
        //     PhantomData<T>,  // this indicates a ownership
        // }
        if adt_def.is_struct() {
            let mut res = self.adt_owner_mut().get_mut(&did).unwrap()[0].clone();
            // Extract all fields in one given struct
            for field in adt_def.all_fields() {
                let field_ty = field.ty(self.tcx(), substs);
                match field_ty.kind() {
                    // Filter the field which is also a struct due to PhantomData<T> is struct
                    TyKind::Adt(field_adt_def, field_substs) => {
                        if field_adt_def.is_phantom_data() {
                            // Extract all generic args in the type
                            for generic_arg in *field_substs {
                                match generic_arg.kind() {
                                    GenericArgKind::Type(g_ty) => {
                                        let mut raw_generic_field_subst =
                                            IsolatedParamFieldSubst::new();
                                        g_ty.visit_with(&mut raw_generic_field_subst);
                                        if raw_generic_field_subst.contains_param() {
                                            {
                                                // To enhance the soundness of phantom unit, the struct should have a
                                                // pointer to store T
                                                let mut has_ptr = false;
                                                for field in adt_def.all_fields() {
                                                    let field_ty = field.ty(self.tcx(), substs);
                                                    let mut find_ptr = FindPtr::new(self.tcx());
                                                    field_ty.visit_with(&mut find_ptr);
                                                    if find_ptr.has_ptr() {
                                                        has_ptr = true;
                                                        break;
                                                    }
                                                }
                                                if has_ptr == false {
                                                    return;
                                                }
                                            }

                                            res.0 = RawTypeOwner::Owned;
                                            self.adt_owner_mut().insert(did, vec![res.clone()]);
                                            return;
                                        }
                                    }
                                    GenericArgKind::Lifetime(..) => {
                                        return;
                                    }
                                    GenericArgKind::Const(..) => {
                                        return;
                                    }
                                }
                            }
                        }
                    }
                    _ => continue,
                }
            }
        }
    }

    #[inline(always)]
    fn extract_owner_prop(&mut self, did: DefId) {
        // Get the definition and subset reference from adt did
        let ty = EarlyBinder::skip_binder(self.tcx().type_of(did));
        let (adt_def, substs) = match ty.kind() {
            TyKind::Adt(adt_def, substs) => (adt_def, substs),
            _ => unreachable!(),
        };

        let mut v_res = self.adt_owner_mut().get_mut(&did).unwrap().clone();

        for (variant_index, variant) in adt_def.variants().iter().enumerate() {
            let res = v_res[variant_index as usize].clone();

            let mut owner_prop = OwnerPropagation::new(self.tcx(), res.0, self.adt_owner());

            for field in &variant.fields {
                let field_ty = field.ty(self.tcx(), substs);
                field_ty.visit_with(&mut owner_prop);
            }
            v_res[variant_index as usize].0 = owner_prop.ownership();
        }

        self.adt_owner_mut().insert(did, v_res);
    }
}

impl<'tcx, 'a> Visitor<'tcx> for TypeAnalysis<'tcx, 'a> {
    fn visit_body(&mut self, body: &Body<'tcx>) {
        for (local, local_decl) in body.local_decls.iter().enumerate() {
            self.visit_local_decl(Local::from(local), local_decl);
        }

        for (block, data) in body.basic_blocks.iter().enumerate() {
            self.visit_basic_block_data(BasicBlock::from(block), data);
        }
    }

    fn visit_basic_block_data(&mut self, _block: BasicBlock, data: &BasicBlockData<'tcx>) {
        let term = data.terminator();
        match &term.kind {
            TerminatorKind::Call { func, .. } => match func {
                Operand::Constant(constant) => match constant.ty().kind() {
                    ty::FnDef(def_id, ..) => {
                        if self.tcx().is_mir_available(*def_id) && self.fn_set_mut().insert(*def_id)
                        {
                            let body = mir_body(self.tcx(), *def_id);
                            self.visit_body(body);
                        }
                    }
                    _ => (),
                },
                _ => (),
            },
            _ => (),
        }
    }

    fn visit_ty(&mut self, ty: Ty<'tcx>, ty_context: TyContext) {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if self.ty_map().get(&ty).is_some() {
                    return;
                }
                self.ty_map_mut().insert(ty, format!("{:?}", ty));
                self.adt_recorder_mut().insert(adtdef.did());

                for field in adtdef.all_fields() {
                    self.visit_ty(field.ty(self.tcx(), substs), copy_ty_context(&ty_context))
                }

                for ty in substs.types() {
                    self.visit_ty(ty, copy_ty_context(&ty_context));
                }
            }
            TyKind::Array(ty, ..) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::Slice(ty) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::RawPtr(ty, _) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::Ref(_, ty, ..) => {
                self.visit_ty(*ty, ty_context);
            }
            TyKind::Tuple(tuple_fields) => {
                for field in tuple_fields.iter() {
                    self.visit_ty(field, copy_ty_context(&ty_context));
                }
            }
            _ => return,
        }
    }

    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        let ty_context = TyContext::LocalDecl {
            local,
            source_info: local_decl.source_info,
        };
        self.visit_ty(local_decl.ty, ty_context);
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for IsolatedParam {
    type Result = ControlFlow<()>;
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::Param(param_ty) => {
                self.record_mut()[param_ty.index as usize] = true;
                ControlFlow::Continue(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for IsolatedParamFieldSubst {
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::Adt(..) => ty.super_visit_with(self),
            TyKind::Param(param_ty) => {
                self.parameters_mut().insert(param_ty.index as usize);
                ControlFlow::Continue(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for IsolatedParamPropagation<'tcx, 'a> {
    // #[inline(always)]
    // fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
    //     Some(self.tcx)
    // }
    type Result = ControlFlow<()>;

    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if substs.len() == 0 {
                    return ControlFlow::Break(());
                }

                if !self.source_enum() && adtdef.is_enum() {
                    return ControlFlow::Break(());
                }

                if !self.unique_mut().insert(adtdef.did()) {
                    return ControlFlow::Continue(());
                }

                let mut map_raw_generic_field_subst = HashMap::new();
                for (index, subst) in substs.iter().enumerate() {
                    match subst.kind() {
                        GenericArgKind::Lifetime(..) => continue,
                        GenericArgKind::Const(..) => continue,
                        GenericArgKind::Type(g_ty) => {
                            let mut raw_generic_field_subst = IsolatedParamFieldSubst::new();
                            g_ty.visit_with(&mut raw_generic_field_subst);
                            if !raw_generic_field_subst.contains_param() {
                                continue;
                            }
                            map_raw_generic_field_subst
                                .insert(index as usize, raw_generic_field_subst);
                        }
                    }
                }
                if map_raw_generic_field_subst.is_empty() {
                    return ControlFlow::Break(());
                }

                let get_ans = self.owner().get(&adtdef.did()).unwrap();
                if get_ans.len() == 0 {
                    return ControlFlow::Break(());
                }
                let get_ans = get_ans[0].clone();

                for (index, flag) in get_ans.1.iter().enumerate() {
                    if *flag && map_raw_generic_field_subst.contains_key(&index) {
                        for elem in map_raw_generic_field_subst
                            .get(&index)
                            .unwrap()
                            .parameters()
                        {
                            self.record[*elem] = true;
                        }
                    }
                }

                for field in adtdef.all_fields() {
                    let field_ty = field.ty(self.tcx(), substs);
                    field_ty.visit_with(self);
                }

                self.unique_mut().remove(&adtdef.did());

                ty.super_visit_with(self)
            }
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for OwnerPropagation<'tcx, 'a> {
    // #[inline(always)]
    // fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
    //     Some(self.tcx)
    // }
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if !self.unique_mut().insert(adtdef.did()) {
                    return ControlFlow::Continue(());
                }

                if adtdef.is_enum() {
                    return ControlFlow::Break(());
                }

                let get_ans = self.owner().get(&adtdef.did()).unwrap();
                if get_ans.len() == 0 {
                    return ControlFlow::Break(());
                }
                let get_ans = get_ans[0].clone();

                match get_ans.0 {
                    RawTypeOwner::Owned => {
                        self.ownership = RawTypeOwner::Owned;
                        return ControlFlow::Break(());
                    }
                    _ => (),
                };

                for field in adtdef.all_fields() {
                    let field_ty = field.ty(self.tcx(), substs);
                    field_ty.visit_with(self);
                }

                self.unique_mut().remove(&adtdef.did());

                ty.super_visit_with(self)
            }
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for FindPtr<'tcx> {
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if adtdef.is_struct() {
                    if !self.unique_mut().insert(adtdef.did()) {
                        return ControlFlow::Continue(());
                    }

                    for field in adtdef.all_fields() {
                        let field_ty = field.ty(self.tcx(), substs);
                        field_ty.visit_with(self);
                    }
                    self.unique_mut().remove(&adtdef.did());
                }
                ControlFlow::Continue(())
            }
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::RawPtr(..) => {
                self.set_ptr(true);
                ControlFlow::Break(())
            }
            TyKind::Ref(..) => {
                self.set_ptr(true);
                ControlFlow::Break(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

impl<'tcx, 'a> TypeVisitor<TyCtxt<'tcx>> for DefaultOwnership<'tcx, 'a> {
    // #[inline(always)]
    // fn tcx_for_anon_const_substs(&self) -> Option<TyCtxt<'tcx>> {
    //     Some(self.tcx)
    // }
    type Result = ControlFlow<()>;
    #[inline(always)]
    fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
        match ty.kind() {
            TyKind::Adt(adtdef, substs) => {
                if adtdef.is_enum() {
                    return ControlFlow::Break(());
                }

                if !self.unique_mut().insert(adtdef.did()) {
                    return ControlFlow::Continue(());
                }

                let get_ans = self.owner().get(&adtdef.did()).unwrap();

                // handle the secene of Zero Sized Types
                if get_ans.len() == 0 {
                    return ControlFlow::Break(());
                }
                let (unit_res, generic_list) = get_ans[0].clone();

                match unit_res {
                    RawTypeOwner::Owned => {
                        self.set_res(RawTypeOwner::Owned);
                        return ControlFlow::Break(());
                    }
                    RawTypeOwner::Unowned => {
                        for (index, each_generic) in generic_list.iter().enumerate() {
                            if *each_generic == false {
                                continue;
                            } else {
                                let subset_ty = substs[index].expect_ty();
                                self.unique_mut().remove(&adtdef.did());
                                subset_ty.visit_with(self);
                            }
                        }
                    }
                    _ => {
                        unreachable!();
                    }
                }
                ControlFlow::Continue(())
            }
            TyKind::Array(..) => ty.super_visit_with(self),
            TyKind::Tuple(..) => ty.super_visit_with(self),
            TyKind::Param(..) => {
                self.set_param(true);
                self.set_res(RawTypeOwner::Owned);
                ControlFlow::Break(())
            }
            TyKind::RawPtr(..) => {
                self.set_ptr(true);
                ControlFlow::Continue(())
            }
            TyKind::Ref(..) => {
                self.set_ptr(true);
                ControlFlow::Continue(())
            }
            _ => ControlFlow::Continue(()),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Default)]
pub struct TyWithIndex<'tcx>(pub Option<(usize, &'tcx TyKind<'tcx>, Option<usize>, bool)>);

impl<'tcx> TyWithIndex<'tcx> {
    pub fn new(ty: Ty<'tcx>, vidx: Option<VariantIdx>) -> Self {
        match &ty.kind() {
            TyKind::Tuple(list) => TyWithIndex(Some((list.len(), &ty.kind(), None, true))),
            TyKind::Adt(adtdef, ..) => {
                if adtdef.is_enum() {
                    if vidx.is_none() {
                        return TyWithIndex(None);
                    }
                    let idx = vidx.unwrap();
                    let len = adtdef.variants()[idx].fields.len();
                    TyWithIndex(Some((len, &ty.kind(), Some(idx.index()), true)))
                } else {
                    let len = adtdef.variants()[VariantIdx::from_usize(0)].fields.len();
                    TyWithIndex(Some((len, &ty.kind(), None, true)))
                }
            }
            TyKind::Array(..) | TyKind::Param(..) | TyKind::RawPtr(..) | TyKind::Ref(..) => {
                TyWithIndex(Some((1, &ty.kind(), None, true)))
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(..)
            | TyKind::Uint(..)
            | TyKind::Float(..)
            | TyKind::Str
            | TyKind::Slice(..) => TyWithIndex(Some((1, &ty.kind(), None, false))),
            _ => TyWithIndex(None),
        }
    }

    // 0->unsupported, 1->trivial, 2-> needed
    pub fn get_priority(&self) -> usize {
        if self.0.is_none() {
            return 0;
        }
        match self.0.unwrap().0 {
            0 => 1,
            _ => match self.0.unwrap().3 {
                true => 2,
                false => 1,
            },
        }
    }
}
