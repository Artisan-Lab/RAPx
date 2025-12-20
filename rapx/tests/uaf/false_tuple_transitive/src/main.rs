fn no_alias_here(s: &str, v: &Vec<usize>) {
    let mut new_v = vec![];
    for element in v {
        new_v.push(element);
    }
    print!("{s} and {new_v:?}");
    // `print!` uses `format!` which will generate a tuple of (&s, &new_v)
}

fn tuple_transitive<T, K> (arg1: T, arg2: K) {
    // test if there is transitive alias:
    // (t, arg1) + (t, arg2) => (arg1, arg2)
    let t = (&arg1, &arg2);
    drop(t);
}

pub fn main() {
    let hello = "hello";
    let some_vec = vec![1, 2, 3];
    no_alias_here(hello, &some_vec);
    tuple_transitive(hello, some_vec);
}
