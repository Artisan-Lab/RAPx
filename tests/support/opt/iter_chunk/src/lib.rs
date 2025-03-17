pub fn foo(v: &mut Vec<i32>) {
    let mut iter = v.iter();
    
    use std::iter::once;

    let r = iter.next();
    let g = iter.next();
    let b = iter.next();
    let a = iter.next();

    Some(once(b).chain(once(g)).chain(once(r)).chain(once(a)));
}

