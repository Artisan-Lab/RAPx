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

fn main(){
    foo1(42);

    let mut x = foo2(42);

    let mut y = 0;
    x = foo3(x, &mut y);
}
fn foo1(mut k:  i32) {
    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        } 
        k+=1;
    }
}
fn foo2(mut k:  i32) -> i32{
    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        } 
        k+=1;
    }
    return k+1;
}
fn foo3(mut k:  i32, y_ref :&mut i32) -> i32{
    while k < 100 {
        let mut i = 0;
        let mut j = k;

        while i < j {
            i += 1;
            j -= 1;
        } 
        k+=1;
        *y_ref = i;

    }
    return k+1;
}