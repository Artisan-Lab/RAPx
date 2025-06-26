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
