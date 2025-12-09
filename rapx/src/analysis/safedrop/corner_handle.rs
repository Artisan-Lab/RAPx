use super::graph::*;
use crate::def_id::*;
use rustc_span::def_id::DefId;

impl<'tcx> SafeDropGraph<'tcx> {
    //these function calls are the functions whose MIRs can not be obtained.
    pub fn corner_handle(
        &mut self,
        _left_ssa: usize,
        _merge_vec: &Vec<usize>,
        def_id: DefId,
    ) -> bool {
        // CASE 1: function::call_mut
        // #![feature(fn_traits)]
        // fn main() {
        //     let x = 1i32;
        //     let mut c = || {x+1;};
        //     c.call_mut(());
        // }
        if def_id == call_mut() || def_id == clone() {
            return true;
        }

        // CASE 3: intrinsic_offset
        // For the latest rust version, this def_id of this function is removed. And we give the example below:
        // #![feature(core_intrinsics)]
        // use std::intrinsics::offset;
        // fn main() {
        //     unsafe {
        //         let x = Box::new(1);
        //         let mut ptr = &x as *const _;
        //         ptr = offset(ptr, 1 as isize);
        //     }
        //
        // }
        //     bb1: {
        //         _4 = &_1;
        //         _3 = &raw const (*_4);
        //         _2 = _3;
        //         _6 = _2;
        //         _7 = const 1_isize;
        //         _5 = Offset(move _6, move _7);
        //         _2 = move _5;
        //         drop(_1) -> [return: bb2, unwind continue];
        //     }
        // if def_id.index.as_usize() == 1709 {
        //     return true;
        // }

        return false;
    }

    //the dangling pointer occuring in some functions like drop() is reasonable.
    pub fn should_check(def_id: DefId) -> bool {
        let mut def_str = format!("{:?}", def_id);
        if let Some(x) = def_str.rfind("::") {
            def_str = def_str.get((x + "::".len())..).unwrap().to_string();
        }
        if let Some(_) = def_str.find("drop") {
            return false;
        }
        if let Some(_) = def_str.find("dealloc") {
            return false;
        }
        if let Some(_) = def_str.find("release") {
            return false;
        }
        if let Some(_) = def_str.find("destroy") {
            return false;
        }
        return true;
    }
}
