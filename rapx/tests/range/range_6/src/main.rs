
pub fn main(){
    let pieces = [42; 8];
    let mut i = 0;
        let slice_index = 8;

    let slice = & pieces[1..slice_index];
        let len = slice.len();

    while i < 2*len {
        let mut val = slice[i]; 
        if val > 128 {
            val+=1;
            // i *= 2;
        } else {
            i *= 21;
        }
    }}