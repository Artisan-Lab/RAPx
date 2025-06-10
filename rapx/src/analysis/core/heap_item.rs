pub mod ownership;
pub mod type_visitor;

use rustc_abi::VariantIdx;
use rustc_middle::ty::EarlyBinder;
use rustc_middle::ty::TypeVisitable;
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind};
use rustc_span::def_id::DefId;

use std::collections::{HashMap, HashSet};
use std::env;

//use stopwatch::Stopwatch;
use crate::analysis::core::heap_item::ownership::OwnershipLayoutResult;
use crate::analysis::rcanary::{rCanary, RcxMut};
use crate::rap_info;
use ownership::RawTypeOwner;

type TyMap<'tcx> = HashMap<Ty<'tcx>, String>;
pub type OwnerUnit = (RawTypeOwner, Vec<bool>);
pub type AdtOwner = HashMap<DefId, Vec<OwnerUnit>>;
type Parameters = HashSet<usize>;
pub type Unique = HashSet<DefId>;
pub type OwnershipLayout = Vec<RawTypeOwner>;
pub type RustBV = Vec<bool>;

// Type Analysis is the first step and it will perform a simple-inter-procedural analysis
// for current crate and collect types after monomorphism as well as extracting 'adt-def'.
// The struct TypeAnalysis implements mir::Visitor to simulate as the type collector.
// Note: the type in this phase is Ty::ty rather of Hir::ty.
pub struct TypeAnalysis<'tcx, 'a> {
    rcx: &'a mut rCanary<'tcx>,
    fn_set: Unique,
    ty_map: TyMap<'tcx>,
    adt_recorder: Unique,
}

impl<'tcx, 'a> TypeAnalysis<'tcx, 'a> {
    pub fn new(rcx: &'a mut rCanary<'tcx>) -> Self {
        Self {
            rcx,
            fn_set: HashSet::new(),
            ty_map: HashMap::new(),
            adt_recorder: HashSet::new(),
        }
    }

    pub fn ty_map(&self) -> &TyMap<'tcx> {
        &self.ty_map
    }

    pub fn ty_map_mut(&mut self) -> &mut TyMap<'tcx> {
        &mut self.ty_map
    }

    pub fn fn_set(&self) -> &Unique {
        &self.fn_set
    }

    pub fn fn_set_mut(&mut self) -> &mut Unique {
        &mut self.fn_set
    }

    pub fn adt_recorder(&self) -> &Unique {
        &self.adt_recorder
    }

    pub fn adt_recorder_mut(&mut self) -> &mut Unique {
        &mut self.adt_recorder
    }

    pub fn adt_owner(&self) -> &AdtOwner {
        self.rcx().adt_owner()
    }

    pub fn adt_owner_mut(&mut self) -> &mut AdtOwner {
        self.rcx_mut().adt_owner_mut()
    }

    // The main phase and the starter function of Type Collector.
    // RAP will construct an instance of struct TypeCollector and call self.start to make analysis starting.
    pub fn start(&mut self) {
        //let mut sw = Stopwatch::start_new();

        // Get the analysis result from rap phase llvm
        // self.connect();
        // Get related adt types through visiting mir local
        self.visitor();

        //rap_info!("AdtDef Sum:{:?}", self.adt_owner().len());
        //rap_info!("Tymap Sum:{:?}", self.ty_map().len());
        //rap_info!("@@@@@@@@@@@@@Type Analysis:{:?}", sw.elapsed_ms());
        //sw.stop();
    }

    pub fn format_owner_unit(unit: &OwnerUnit) -> String {
        let (owner, flags) = unit;
        let vec_str = flags
            .iter()
            .map(|&b| if b { "1" } else { "0" })
            .collect::<Vec<_>>()
            .join(",");
        format!("({}, [{}])", owner, vec_str)
    }

    pub fn output(&mut self) {
        for elem in self.adt_owner() {
            let name = format!(
                "{:?}",
                EarlyBinder::skip_binder(self.rcx.tcx().type_of(*elem.0))
            );
            let owning = elem
                .1
                .iter()
                .map(Self::format_owner_unit)
                .collect::<Vec<_>>()
                .join(", ");
            rap_info!("{} {}", name, owning);
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Encoder;

impl<'tcx> Encoder {
    pub fn encode(
        rcx: &rCanary<'tcx>,
        ty: Ty<'tcx>,
        variant: Option<VariantIdx>,
    ) -> OwnershipLayoutResult {
        match ty.kind() {
            TyKind::Array(..) => {
                let mut res = OwnershipLayoutResult::new();
                let mut default_ownership = DefaultOwnership::new(rcx.tcx(), rcx.adt_owner());

                let _ = ty.visit_with(&mut default_ownership);
                res.update_from_default_ownership_visitor(&mut default_ownership);

                res
            }
            TyKind::Tuple(tuple_ty_list) => {
                let mut res = OwnershipLayoutResult::new();

                for tuple_ty in tuple_ty_list.iter() {
                    let mut default_ownership = DefaultOwnership::new(rcx.tcx(), rcx.adt_owner());

                    let _ = tuple_ty.visit_with(&mut default_ownership);
                    res.update_from_default_ownership_visitor(&mut default_ownership);
                }

                res
            }
            TyKind::Adt(adtdef, substs) => {
                // check the ty is or is not an enum and the variant of this enum is or is not given
                if adtdef.is_enum() && variant.is_none() {
                    return OwnershipLayoutResult::new();
                }

                let mut res = OwnershipLayoutResult::new();

                // check the ty if it is a struct or union
                if adtdef.is_struct() || adtdef.is_union() {
                    for field in adtdef.all_fields() {
                        let field_ty = field.ty(rcx.tcx(), substs);

                        let mut default_ownership =
                            DefaultOwnership::new(rcx.tcx(), rcx.adt_owner());

                        let _ = field_ty.visit_with(&mut default_ownership);
                        res.update_from_default_ownership_visitor(&mut default_ownership);
                    }
                }
                // check the ty which is an enum with a exact variant idx
                else if adtdef.is_enum() {
                    let vidx = variant.unwrap();

                    for field in &adtdef.variants()[vidx].fields {
                        let field_ty = field.ty(rcx.tcx(), substs);

                        let mut default_ownership =
                            DefaultOwnership::new(rcx.tcx(), rcx.adt_owner());

                        let _ = field_ty.visit_with(&mut default_ownership);
                        res.update_from_default_ownership_visitor(&mut default_ownership);
                    }
                }
                res
            }
            TyKind::Param(..) => {
                let mut res = OwnershipLayoutResult::new();
                res.set_requirement(true);
                res.set_param(true);
                res.set_owned(true);
                res.layout_mut().push(RawTypeOwner::Owned);
                res
            }
            TyKind::RawPtr(..) => {
                let mut res = OwnershipLayoutResult::new();
                res.set_requirement(true);
                res.layout_mut().push(RawTypeOwner::Unowned);
                res
            }
            TyKind::Ref(..) => {
                let mut res = OwnershipLayoutResult::new();
                res.set_requirement(true);
                res.layout_mut().push(RawTypeOwner::Unowned);
                res
            }
            _ => OwnershipLayoutResult::new(),
        }
    }
}

/// We encapsulate the interface for identifying heap items in a struct named `HeapItem`.
/// This struct is a zero-sized type (ZST), so creating and using it does not incur any overhead.
/// These interfaces typically take at least two fixed inputs.
/// One is the context metadata of `rCanary`, which stores the cache for ADT analysis
/// (of course, users do not need to know the specific information stored).
/// The second input is the type that the user needs to process, along with other parameters.
#[derive(Copy, Clone, Debug)]
pub struct HeapItem;

impl HeapItem {
    /// This method is used to check if one adt-def is already a heap item.
    /// It is a summary of one type which demonstrate that we will consider all the fields/variants,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> {
    ///    buf: RawVec<T, A>, // this field is a heap item
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::HeapItem;
    ///  let ans = HeapItem::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_adt<'tcx>(rcx: &rCanary<'tcx>, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.0 == RawTypeOwner::Owned {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the struct is already a heap item.
    /// It is a summary of one type which demonstrate that we will consider all the fields,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of an enum type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> {
    ///    buf: RawVec<T, A>, // this field is a heap item
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_struct(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_struct<'tcx>(rcx: &rCanary<'tcx>, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_struct() && !adtdef.is_union() {
                    return Err("The input is not a struct");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                if ans[0].0 == RawTypeOwner::Owned {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the enum is already a heap item.
    /// It is a summary of one type which demonstrate that we will consider all the variants,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    /// Note that, even for each variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T>` the result is `Ok(true)`.
    /// ```rust
    /// pub enum MyBuf<T> {
    ///    Buf1(Vec<T>), // this variance is a heap item
    ///    Buf2(Vec<T>), // this variance is a heap item
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_enum(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum<'tcx>(rcx: &rCanary<'tcx>, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.0 == RawTypeOwner::Owned {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one variance of the enum is already a heap item.
    /// It is a summary of one variance which demonstrate that we will consider all the fields of it,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    /// If the index `idx` is not valid (out of bound), the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T>` the result for idx: 0, 1 is `Ok(true)`; the result for idx: 3 is `Err`.
    /// ```rust
    /// pub enum MyBuf<T> {
    ///    Buf1(Vec<T>), // this variance is a heap item
    ///    Buf2(Vec<T>), // this variance is a heap item
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_enum_vidx(rcanary.rcx, vec.ty, 1);
    /// ```
    pub fn is_enum_vidx<'tcx>(
        rcx: &rCanary<'tcx>,
        ty: Ty<'tcx>,
        idx: usize,
    ) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                if idx > ans.len() {
                    return Err("The index is not a valid variance");
                }
                if ans[idx].0 == RawTypeOwner::Owned {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to give the result of all the variances of the enum.
    /// For each variance, it is a summary that we will consider all the fields of it,
    /// although the analyzer will not traverse them (thus overhead is cheap).
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T>` the result is `[true, false]`.
    /// ```rust
    /// pub enum MyBuf<T> {
    ///    Buf1(Vec<T>), // this variance is a heap item
    ///    Buf2(()), // this variance is a heap item
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    /// use rap::analysis::core::heap_item::HeapItem;
    /// let ans = HeapItem::is_enum_flattened(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum_flattened<'tcx>(
        rcx: &rCanary<'tcx>,
        ty: Ty<'tcx>,
    ) -> Result<Vec<bool>, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                let mut v = Vec::with_capacity(ans.len());
                for i in ans.iter() {
                    if i.0 == RawTypeOwner::Owned {
                        v.push(true);
                    } else {
                        v.push(false);
                    }
                }
                Ok(v)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}

/// We encapsulate the interface for identifying isolated parameters in a struct named `IsolatedParameter`.
/// This struct is a zero-sized type (ZST), so creating and using it does not incur any overhead.
/// These interfaces typically take at least two fixed inputs.
/// One is the context metadata of `rCanary`, which stores the cache for ADT analysis
/// (of course, users do not need to know the specific information stored).
/// The second input is the type that the user needs to process, along with other parameters.
pub struct IsolatedParameter;

impl IsolatedParameter {
    /// This method is used to check if one adt-def has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics.
    /// Those generic parameters can be located in different fields/variants, and some of them can be
    /// found in multiple fields/variants.
    /// The analyzer will not traverse them to generate the result (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> { // parameter A is an isolated parameter
    ///    buf: RawVec<T, A>,  // parameter A inside in RawVec
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_adt<'tcx>(rcx: &rCanary<'tcx>, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.1.iter().any(|&x| x == true) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the struct has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics.
    /// Those generic parameters can be located in different fields, and some of them can be
    /// found in multiple fields.
    /// The analyzer will not traverse them to generate the result (thus overhead is cheap).
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyVec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub struct MyVec<T, A: Allocator = Global> { // parameter A is an isolated parameter
    ///    buf: RawVec<T, A>, // parameter A inside in RawVec
    ///    len: usize,
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_struct<'tcx>(rcx: &rCanary<'tcx>, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_struct() && !adtdef.is_union() {
                    return Err("The input is not a struct");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                if ans[0].1.iter().any(|&x| x == true) {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the enum has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics in all the variants.
    /// Those generic parameters can be located in different fields, and some of them can be
    /// found in multiple fields.
    /// Note that, even for each variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T, S, F>` the result is `Ok(true)`.
    /// ```rust
    /// pub enum MyBuf<T, S, F> { // parameter S F are an isolated parameters
    ///    Buf1(Vec<T>),
    ///    Buf2(S), // this variance is an isolated parameter
    ///    Buf3((F,S)), // this variance has 2 isolated parameters
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_adt(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum<'tcx>(rcx: &rCanary<'tcx>, ty: Ty<'tcx>) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                for i in ans.iter() {
                    if i.1.iter().any(|&x| x == true) {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one variance of the enum has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics in the given variance.
    /// Note that, even for this variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    /// If the index `idx` is not valid (out of bound), the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `MyBuf<T, S, F>` the result for idx: 0 is `Ok(false)`; the result for idx: 1, 2 is `Ok(true)`; the result for idx: 3 is `Err`.
    /// ```rust
    /// pub enum MyBuf<T, S, F> { // parameter S F are an isolated parameters
    ///    Buf1(Vec<T>),
    ///    Buf2(S), // this variance is an isolated parameter
    ///    Buf3((F,S)), // this variance has 2 isolated parameters
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_enum_vidx(rcanary.rcx, vec.ty, 1);
    /// ```
    pub fn is_enum_vidx<'tcx>(
        rcx: &rCanary<'tcx>,
        ty: Ty<'tcx>,
        idx: usize,
    ) -> Result<bool, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                if idx > ans.len() {
                    return Err("The index is not a valid variance");
                }
                if ans[idx].1.iter().any(|&x| x == true) {
                    return Ok(true);
                }
                Ok(false)
            }
            _ => Err("The input is not an ADT"),
        }
    }

    /// This method is used to check if one adt-def of the enum has at least one isolated parameter.
    /// It is a summary of one type which demonstrate that we will consider all the generics in all the variants.
    /// Those generic parameters can be located in different fields, and some of them can be
    /// found in multiple fields.
    /// Note that, even for each variance, the result also analyze all its fields.
    /// It can be referred to the enum with enum-type variance.
    ///
    /// # Safety
    /// If `ty` is not an adt, the result is `Err`.
    /// If the input is the def of a struct type, the result is `Err`.
    ///
    /// # Case `ty::Ty`
    /// Given the adt `Vec<T, A>` the result is `Ok(true)`.
    /// ```rust
    /// pub enum MyBuf<T, S, F> { // parameter S F are an isolated parameters
    ///    Buf1(Vec<T>),
    ///    Buf2(S), // this variance is an isolated parameter
    ///    Buf3((F,S)), // this variance has 2 isolated parameters
    /// }
    /// ```
    ///
    /// # Example:
    /// ```rust
    ///  use rap::analysis::core::heap_item::IsolatedParameter;
    ///  let ans = IsolatedParameter::is_enum_flattened(rcanary.rcx, vec.ty);
    /// ```
    pub fn is_enum_flattened<'tcx>(
        rcx: &rCanary<'tcx>,
        ty: Ty<'tcx>,
    ) -> Result<Vec<Vec<bool>>, &'static str> {
        match ty.kind() {
            TyKind::Adt(adtdef, ..) => {
                if !adtdef.is_enum() {
                    return Err("The input is not an enum");
                }
                let ans = rcx.adt_owner().get(&adtdef.0 .0.did).unwrap();
                let mut v: Vec<Vec<bool>> = Vec::default();
                for i in ans.iter() {
                    v.push(i.1.clone());
                }
                Ok(v)
            }
            _ => Err("The input is not an ADT"),
        }
    }
}

impl<'tcx, 'o, 'a> RcxMut<'tcx, 'o, 'a> for TypeAnalysis<'tcx, 'a> {
    #[inline(always)]
    fn rcx(&'o self) -> &'o rCanary<'tcx> {
        self.rcx
    }

    #[inline(always)]
    fn rcx_mut(&'o mut self) -> &'o mut rCanary<'tcx> {
        &mut self.rcx
    }

    #[inline(always)]
    fn tcx(&'o self) -> TyCtxt<'tcx> {
        self.rcx().tcx()
    }
}

#[derive(Clone)]
struct IsolatedParam {
    record: Vec<bool>,
}

impl IsolatedParam {
    pub fn new(len: usize) -> Self {
        Self {
            record: vec![false; len],
        }
    }

    pub fn record_mut(&mut self) -> &mut Vec<bool> {
        &mut self.record
    }
}

#[derive(Clone)]
struct IsolatedParamFieldSubst {
    parameters: Parameters,
}

impl<'tcx> IsolatedParamFieldSubst {
    pub fn new() -> Self {
        Self {
            parameters: HashSet::new(),
        }
    }

    pub fn parameters(&self) -> &Parameters {
        &self.parameters
    }

    pub fn parameters_mut(&mut self) -> &mut Parameters {
        &mut self.parameters
    }

    pub fn contains_param(&self) -> bool {
        !self.parameters.is_empty()
    }
}

#[derive(Clone)]
struct IsolatedParamPropagation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    record: Vec<bool>,
    unique: Unique,
    source_enum: bool,
    ref_adt_owner: &'a AdtOwner,
}

impl<'tcx, 'a> IsolatedParamPropagation<'tcx, 'a> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        record: Vec<bool>,
        source_enum: bool,
        ref_adt_owner: &'a AdtOwner,
    ) -> Self {
        Self {
            tcx,
            record,
            unique: HashSet::new(),
            source_enum,
            ref_adt_owner,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn record_mut(&mut self) -> &mut Vec<bool> {
        &mut self.record
    }

    pub fn unique_mut(&mut self) -> &mut Unique {
        &mut self.unique
    }

    pub fn source_enum(&mut self) -> bool {
        self.source_enum
    }

    pub fn owner(&self) -> &'a AdtOwner {
        self.ref_adt_owner
    }
}

#[derive(Clone)]
struct OwnerPropagation<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    ownership: RawTypeOwner,
    unique: Unique,
    ref_adt_owner: &'a AdtOwner,
}

impl<'tcx, 'a> OwnerPropagation<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, ownership: RawTypeOwner, ref_adt_owner: &'a AdtOwner) -> Self {
        Self {
            tcx,
            ownership,
            unique: HashSet::new(),
            ref_adt_owner,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn ownership(&self) -> RawTypeOwner {
        self.ownership
    }

    pub fn unique_mut(&mut self) -> &mut Unique {
        &mut self.unique
    }

    pub fn owner(&self) -> &'a AdtOwner {
        self.ref_adt_owner
    }
}

#[derive(Clone)]
pub struct DefaultOwnership<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    unique: Unique,
    ref_adt_owner: &'a AdtOwner,
    res: RawTypeOwner,
    param: bool,
    ptr: bool,
}

impl<'tcx, 'a> DefaultOwnership<'tcx, 'a> {
    pub fn new(tcx: TyCtxt<'tcx>, ref_adt_owner: &'a AdtOwner) -> Self {
        Self {
            tcx,
            unique: HashSet::new(),
            ref_adt_owner,
            res: RawTypeOwner::Unowned,
            param: false,
            ptr: false,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn unique(&self) -> &Unique {
        &self.unique
    }

    pub fn unique_mut(&mut self) -> &mut Unique {
        &mut self.unique
    }

    pub fn get_res(&self) -> RawTypeOwner {
        self.res
    }

    pub fn set_res(&mut self, res: RawTypeOwner) {
        self.res = res;
    }

    pub fn is_owning_true(&self) -> bool {
        self.res == RawTypeOwner::Owned
    }

    pub fn get_param(&self) -> bool {
        self.param
    }

    pub fn set_param(&mut self, p: bool) {
        self.param = p;
    }

    pub fn is_param_true(&self) -> bool {
        self.param == true
    }

    pub fn get_ptr(&self) -> bool {
        self.ptr
    }

    pub fn set_ptr(&mut self, p: bool) {
        self.ptr = p;
    }

    pub fn is_ptr_true(&self) -> bool {
        self.ptr == true
    }

    pub fn owner(&self) -> &'a AdtOwner {
        self.ref_adt_owner
    }
}

#[derive(Clone)]
pub struct FindPtr<'tcx> {
    tcx: TyCtxt<'tcx>,
    unique: Unique,
    ptr: bool,
}

impl<'tcx> FindPtr<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            unique: Unique::default(),
            ptr: false,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn unique(&self) -> &Unique {
        &self.unique
    }

    pub fn unique_mut(&mut self) -> &mut Unique {
        &mut self.unique
    }

    pub fn has_ptr(&self) -> bool {
        self.ptr
    }

    pub fn set_ptr(&mut self, ptr: bool) {
        self.ptr = ptr;
    }
}

pub fn is_display_verbose() -> bool {
    match env::var_os("ADT_DISPLAY") {
        Some(_) => true,
        _ => false,
    }
}
pub fn mir_body(tcx: TyCtxt<'_>, def_id: DefId) -> &rustc_middle::mir::Body<'_> {
    //let def = ty::InstanceDef::Item(def_id);
    let def = ty::InstanceKind::Item(def_id);
    tcx.instance_mir(def)
}

#[derive(Debug, Clone, Hash, Eq, PartialEq, Default)]
pub struct IndexedTy<'tcx>(pub Option<(usize, &'tcx TyKind<'tcx>, Option<usize>, bool)>);

impl<'tcx> IndexedTy<'tcx> {
    pub fn new(ty: Ty<'tcx>, vidx: Option<VariantIdx>) -> Self {
        match &ty.kind() {
            TyKind::Tuple(list) => IndexedTy(Some((list.len(), &ty.kind(), None, true))),
            TyKind::Adt(adtdef, ..) => {
                if adtdef.is_enum() {
                    if vidx.is_none() {
                        return IndexedTy(None);
                    }
                    let idx = vidx.unwrap();
                    let len = adtdef.variants()[idx].fields.len();
                    IndexedTy(Some((len, &ty.kind(), Some(idx.index()), true)))
                } else {
                    let len = adtdef.variants()[VariantIdx::from_usize(0)].fields.len();
                    IndexedTy(Some((len, &ty.kind(), None, true)))
                }
            }
            TyKind::Array(..) | TyKind::Param(..) | TyKind::RawPtr(..) | TyKind::Ref(..) => {
                IndexedTy(Some((1, &ty.kind(), None, true)))
            }
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(..)
            | TyKind::Uint(..)
            | TyKind::Float(..)
            | TyKind::Str
            | TyKind::Slice(..) => IndexedTy(Some((1, &ty.kind(), None, false))),
            _ => IndexedTy(None),
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
