pub fn find_lu_slength(a: &[u8], b: &[u8]) -> i64 {
    let mut same = true;

    if a.len() != b.len() {
        same = false;
    } else {
        let mut i: usize = 0;
        while i < a.len() {
            if a[i] != b[i] {
                same = false;
            }
            i += 1;
        }
    }

    if same {
        return -1;
    }

    let la = a.len() as i64;
    let lb = b.len() as i64;

    if la > lb {
        la
    } else {
        lb
    }
}
