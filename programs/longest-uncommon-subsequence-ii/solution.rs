pub fn find_lu_slength(strs: &[Vec<u8>]) -> i64 {
    let n: usize = strs.len();
    let mut best: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        let needle = &strs[i];
        let mut uncommon: bool = true;
        let mut j: usize = 0;

        while j < n {
            if j != i {
                let hay = &strs[j];
                let mut a: usize = 0;
                let mut b: usize = 0;

                while a < needle.len() && b < hay.len() {
                    if needle[a] == hay[b] {
                        a += 1;
                    }
                    b += 1;
                }

                if a == needle.len() {
                    uncommon = false;
                }
            }
            j += 1;
        }

        if uncommon {
            let len_i: i64 = needle.len() as i64;
            if len_i > best {
                best = len_i;
            }
        }

        i += 1;
    }

    best
}
