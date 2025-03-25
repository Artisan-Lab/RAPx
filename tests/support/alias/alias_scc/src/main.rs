enum Selector {
    First,
    Second,
}

//Expected alias analysis result: (1,0)
fn foo<'a>(x: &'a i32, y: &'a i32, choice: Selector) -> &'a i32 {
    let mut r = x;
    while *r > 1 {
        let a = match choice {
            Selector::First => x,
            Selector::Second => y,
        };
        r = match choice {
            Selector::First => a,
            Selector::Second => x,
        };
    }
    return r;
}

fn main() {
    let a = 1;
    let b = 2;
    let _result = foo(&a, &b, Selector::First);
}
