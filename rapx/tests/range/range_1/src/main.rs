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
fn main() {
    let mut k = 0;

    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        }

        k += 1;
    }
}
// fn main() {
//     let mut k = 0;

//     while k < 100 {
//         let mut i = 0;
//         let mut j = k;

//         while i < j {
//             i += 1;
//             j -= 1;
//         }

//         k += 1;
//     }
// }
// fn main() -> () {
//     let mut _0: ();
//     let mut _1: i32;
//     let mut _2: bool;
//     let mut _3: i32;
//     let mut _6: bool;
//     let mut _7: i32;
//     let mut _8: i32;
//     scope 1 {
//         debug k => _1;
//         let mut _4: i32;
//         scope 2 {
//             debug i => _4;
//             let mut _5: i32;
//             scope 3 {
//                 debug j => _5;
//             }
//         }
//     }

//     bb0: {
//         _1 = const 0_i32;
//         goto -> bb1;
//     }

//     bb1: {
//         _3 = copy _1;
//         _2 = Lt(move _3, const 100_i32);
//         switchInt(move _2) -> [0: bb6, otherwise: bb2];
//     }

//     bb2: {
//         _4 = const 0_i32;
//         _5 = copy _1;
//         goto -> bb3;
//     }

//     bb3: {
//         _7 = copy _4;
//         _8 = copy _5;
//         _6 = Lt(move _7, move _8);
//         switchInt(move _6) -> [0: bb5, otherwise: bb4];
//     }

//     bb4: {
//         _4 = Add(copy _4, const 1_i32);
//         _5 = Sub(copy _5, const 1_i32);
//         goto -> bb3;
//     }

//     bb5: {
//         _1 = Add(copy _1, const 1_i32);
//         goto -> bb1;
//     }

//     bb6: {
//         return;
//     }
// }
