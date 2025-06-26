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
fn foo() ->i32{
    let mut k = 0;

    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        }
        if i<=j{
            k += 1;
            return i;
        }
        k += 1;
        
    }
    return k+1;
}
fn main(){
    foo();
}
// fn main() {
//     let mut x = 0;
//     let mut y = 0;
//     while x < 100 {
//         y += 2;
//         x+=1;
//     }
// }

// fn foo1()  {
//     let mut x = 0;
//     let mut y = 0;
//     while x < 100 {
//         y += 2;
//         x+=1;
//     }
// }