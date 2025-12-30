#[derive(Debug)]
struct Leaf {
    value: Box<i32>,
}

#[derive(Debug)]
struct Node {
    leaf1: Box<Leaf>,
    leaf2: Box<Leaf>,
    weight: i32,
}

#[derive(Debug)]
struct Middle {
    node1: Box<Node>,
    node2: Box<Node>,
    leaf: Box<Leaf>,
    bias: i32,
}

#[derive(Debug)]
struct Root {
    middle: Box<Middle>,
    offset: i32,
}

fn foo(c: usize, root: &Root) -> &Leaf {
    if c == 0 {
        &root.middle.leaf
    } else {
        &root.middle.node2.leaf2
    }
}
