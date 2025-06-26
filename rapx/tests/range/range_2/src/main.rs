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
    let mut x = 0;
    let mut y = 0;
    while x < 100 {
        y += 2;
        x+=1;
    }
}

fn foo1() {
    let mut x = 0;
    let mut y = 0;
    while x < 100 {
        y += 2;
        x+=1;
    }
}