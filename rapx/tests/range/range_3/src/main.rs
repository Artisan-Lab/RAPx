
pub struct SSAstmt;
pub struct ESSAstmt;
// testcase for the path constraints analysis
fn main() {
    let x = 1;
    let mut y = 10;
    let mut z = 0;
    if x < y {
        y += 1;
}
else{
   y -= 1;
   if y > z {
       y -= 2;
   } else {
       y += 2;
   }
}
}