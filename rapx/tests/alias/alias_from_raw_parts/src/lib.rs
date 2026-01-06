#[allow(unused)]

fn foo(p: *mut u8) -> Vec<u8> {
    unsafe { Vec::from_raw_parts(p, 1, 1) }
}
