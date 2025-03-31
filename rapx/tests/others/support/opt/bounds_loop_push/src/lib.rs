pub fn foo(u: &mut Vec<i32>) -> Vec<i32> {
    let mut v = Vec::new();
    for i in u {
        v.push(*i + 1);
    }
    v
}