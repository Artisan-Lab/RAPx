use std::collections::HashSet;

fn foo(a: &Vec<String>) {
    let mut b = HashSet::new();
    for i in a {
        let c = i.clone();
        b.insert(c);
    }
}
