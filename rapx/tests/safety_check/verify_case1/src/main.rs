#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#[derive(Debug, Clone)]
struct SecretRegion {
    buffer: Vec<u32>,
    size: usize,
}

#[rapx::inner(property = ValidPtr(ptr, u32, 1), kind = "precond")]
#[rapx::inner(property = Aligned (ptr, u32), kind = "precond")]
#[rapx::inner(property = Init(ptr, u32, 1), kind = "precond")]
#[rapx::inner(property = Allocated(region.buffer, u32, region.size), kind = "precond")]
#[rapx::inner(property = Init(region.buffer, u32, region.size), kind = "precond")]
pub fn xor_secret_region(
    ptr: *mut u32,
    offset: isize,
    region: SecretRegion
) -> u32 {
    unsafe {
    let mut src_value = ptr.read();
    let secret_ptr = region.buffer.as_ptr();
    let secret_region = secret_ptr.offset(offset);
    let secret_value = secret_region.read();
    src_value ^= secret_value;
    src_value
    }
    
}

fn main() {
    
}