// use std::ptr;
use std::slice;
// use std::mem::MaybeUninit;

// struct MySliceWrapperTest<T> {
//     data: *const T, 
//     len: usize,     
// }

// impl<T> MySliceWrapperTest<T> {
//     fn new() -> Self {
//         let uninit_data = MaybeUninit::<[T; 10]>::uninit();
//         let data = uninit_data.as_ptr() as *const T;
//         MySliceWrapperTest { data, len: 10 }
//     }

//     fn get_slice(&self, offset: usize, length: usize) -> &[T] {
//         assert!(offset + length <= self.len, "Requested slice is out of bounds");
//         let adjusted_data = unsafe { self.data.add(offset) };
//         // Fail(Allocated): 'adjusted_data' points to uninit memory
//         // Fail(Aligned): 'adjusted_data' may be not aligned due to the offset
//         unsafe { slice::from_raw_parts(adjusted_data, length) }
//     }
// }


// fn test1() {
//     let len: usize = 0;
//     let data = ptr::null::<i32>();
//     // Fail(Allocated): 'data' is null, which violates the requirement that it must be non-null
//     let slice: &[i32] = unsafe { slice::from_raw_parts(data, len) };
// }

// fn test2() {
//     let len: usize = 3;
//     let uninit_data = MaybeUninit::<[i32; 3]>::uninit();
//     let data = uninit_data.as_ptr() as *const i32;
//     // Fail(Initialized): 'data' points to uninitialized memory, which violates the initialization requirement
//     let slice: &[i32] = unsafe { slice::from_raw_parts(data, len) };
//     println!("First element: {}", slice[0]);
// }

// fn test3() {
//     let part1 = Box::new(1);
//     let part2 = Box::new(2);
//     let data = [Box::into_raw(part1), Box::into_raw(part2)].as_ptr() as *const i32;
//     let len = 2;
//     // Fail(Dereferencable): 'data' points across multiple allocated objects, violating the single allocation constraint
//     let slice: &[i32] = unsafe { slice::from_raw_parts(data, len) };
//     println!("Slice elements: {:?}", slice);
// }

// fn test4() {
//     let unaligned = [0u8; 5];
//     let data = unaligned.as_ptr().wrapping_offset(1) as *const i32;
//     let len = 1;
//     // Fail(Layout): 'data' is not aligned, violating the alignment requirement
//     let slice: &[i32] = unsafe { slice::from_raw_parts(data, len) };
//     println!("Slice elements: {:?}", slice);
// }

// fn test5(offset:usize) {
//     let unaligned = [0u32; 5];
//     let ptr = unaligned.as_ptr() as *const u8;
//     let data = unsafe { ptr.add(offset) as *const i32 };
//     let len = 1;
//     // Fail(Layout): 'data' is not aligned, violating the alignment requirement
//     let slice: &[i32] = unsafe { slice::from_raw_parts(data, len) };
//     println!("Slice elements: {:?}", slice);
// }


/// offset: _1 
/// unaligned: _2
/// unaligned.as_ptr(): _4
/// ptr: _3
/// data: _7 _12
 unsafe fn test5(_offset:usize) {
    let unaligned = [0u32; 5];
    let ptr = unaligned.as_ptr() as *const u8;
    let data = ptr as *mut i32;
    let len = 1;
    // Fail(Layout): 'data' is not aligned, violating the alignment requirement
    let _slice: &[i32] = slice::from_raw_parts_mut(data, len);
    // println!("Slice elements: {:?}", slice);
}

// fn test5() {
//     let data: *const u8 = Box::leak(Box::new(0));
//     let len: usize = (isize::MAX as usize) / std::mem::size_of::<u8>() + 1;
//     // Pass(Allocated \ Aligned):   data is allocated and aligned
//     // Fail(Bounded): 'len' is out of the max value
//     // Fail(Dereferencable \ Initialized): 'data' onnly points to the memory with a 'u8' size, but the 'len' is out of this range
//     let slice: &[u8] = unsafe { slice::from_raw_parts(data, len) };
//     if let Some(last_element) = slice.last() {
//         println!("Last element: {}", last_element);
//     } else {
//         println!("Slice is empty");
//     }
// }


pub trait MySpecialTrait2 {
    fn is_special(&self) -> bool;
}
impl MySpecialTrait2 for i8 {
    fn is_special(&self) -> bool { *self > 0 }
}
impl MySpecialTrait2 for f64 {
    fn is_special(&self) -> bool { self.is_sign_positive() }
}

pub trait MySpecialTrait {
    fn is_special(&self) -> bool;
}
impl MySpecialTrait for i8 {
    fn is_special(&self) -> bool { *self > 0 }
}
impl MySpecialTrait for f32 {
    fn is_special(&self) -> bool { self.is_sign_positive() }
}


pub fn test6<T: MySpecialTrait2 + Copy, U: MySpecialTrait + Copy>(a: &mut [T], _b: &[U; 20]) {
    unsafe {
        let _c = std::slice::from_raw_parts_mut(a.as_mut_ptr() as *mut U, 20);
        // for i in 0..20 {
        //     c[i] ^= b[i];
        // }
    }
}

pub fn test7(a: &mut [u8], b: &[u32; 20]) {
    unsafe {
        let c = slice::from_raw_parts_mut(a.as_mut_ptr() as *mut u32, 20);
        for i in 0..20 {
            c[i] ^= b[i];
        }
    }
}

fn main() {
    unsafe {test5(3)};
    let mut x = [0u8;40];
    let y = [0u32;20];
    test7(&mut x[1..32], &y);
}
