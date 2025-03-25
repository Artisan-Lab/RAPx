/*
 * This is a buggy case: create_vec() returns a dangling pointer
 */

//fn unsafe create_vec() -> *mut Vec<i32> {// marking the function as unsafe is also inappropriate
fn create_vec() -> *mut Vec<i32> {
    let mut v = Vec::new();
    //Fix: let mut v = Box::new(Vec::new());
    v.push(1);
    &mut v as *mut Vec<i32>
    //Fix: Box::into_raw(v)
}

fn main() {
    let p = create_vec();
    //  let v = unsafe {&mut *p};
    //  v.push(4);
    //  println!("{:?}", v);
}
