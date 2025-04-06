fn foo(mut a: Vec<i32>) {
    for i in 0..a.len() {
        a[i] = a[i] + 1;
    }
}