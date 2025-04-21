fn foo(mut a: Vec<i32>) {
    for i in 0..a.len() {
        a[i] = a[i] + 1;
    }
}

fn foo1(input: &[u8]) {
    let mut index = 0;
    let len = input.len();
    while index < len {
        let b = input[index];
        index += 1;
    }
}