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
    let para = 42;
    foo1(para);
    let para2 = 52;
    let mut x = foo2(55, para2);

    let mut y = 0;
    // x = foo3(x, &mut y);
}
fn foo1(mut k:  usize) {
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
fn foo2(mut k:  usize,c:usize) -> usize{
    
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
// fn foo3(mut k:  usize, y_ref :&mut usize) -> usize{
//     while k < 100 {
//         let mut i = 0;
//         let mut j = k;

//         while i < j {
//             i += 1;
//             j -= 1;
//         } 
//         k+=1;
//         *y_ref = i;

//     }
//     return k+1;
// }