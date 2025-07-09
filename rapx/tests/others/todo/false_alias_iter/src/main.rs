// p and 0 should not be alias in this case.
fn foo(p:&[u8]) -> Vec<u8>{
    p.iter().map(|x| x + 1).collect()
}

fn main() {
    let v1 = vec![1,2,3];
    let v2 = foo(&v1);
    println!("{:?}",v1);
    println!("{:?}",v2);
}
