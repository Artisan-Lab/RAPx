fn foo(a: Vec<i32>, b: Vec<i32>) {
    for i in b.iter() {
        if a.contains(i) {}
    }
}