// fn test1() {
//     let mut x = 0;

//     while x < 10 {
//         x += 1;
//     }
// }
pub struct SSAstmt;
pub struct ESSAstmt;

#[used]
static _SSAstmt: Option<SSAstmt> = None;
static _ESSAstmt: Option<ESSAstmt> = None;
// struct Item<'a>(&'a str);

// #[derive(Debug)]
// struct Iter {
//     ptr: *const str,
// }

// impl<'a> Iter {
//     fn new(item: Item<'a>) -> Iter {
//         Iter { ptr: item.0 }
//     }
// }

// fn main() {
//     let x = Item("as");
//     let x = Iter::new(x);
//     println!("{:?}", x);
// }
enum Selector {
    First,
    Second,
}

//Expected alias analysis result: (1,0)
// fn foo<'a>(x: &'a i32, y: &'a i32, choice: Selector) -> &'a i32 {
//     let a = match choice {
//         Selector::First => x,
//         Selector::Second => y,
//     };
//     match choice {
//         Selector::First => a,
//         Selector::Second => x,
//     }
// }

fn main() {
    let mut x = 0;
    foo(&mut x);
    x+= 1;
    // let mut y = 0;
    // foo(&mut y);

}
fn  foo(x_ref: &mut i32)  {
    *x_ref += 1;

}
fn  foo1(a:i32,b:i32,c:i32,d:i32) -> i32 {
    let mut x = a + b;
    x += c + d;
    x

    

}