struct Point {
    x: i32,
    y: i32,
}

//Expected alias analysis result: (1.0, 1.1, 0)
fn foo(p1: &Point) -> &i32 {
    if p1.x > 0 {
        &p1.x
    } else {
        &p1.y
    }
}

fn main() {
    let p = Box::new(Point { x: 10, y: 20 });
    let _r = foo(&p);
}
