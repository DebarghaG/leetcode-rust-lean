pub fn prefix_count(words: &[Vec<u8>], pref: &[u8]) -> i64 {
    let mut count: i64 = 0;
    let n = words.len();
    let m = pref.len();

    let mut i: usize = 0;
    while i < n {
        let w = &words[i];
        let mut ok: bool = true;

        if w.len() < m {
            ok = false;
        } else {
            let mut j: usize = 0;
            while j < m {
                if w[j] != pref[j] {
                    ok = false;
                }
                j += 1;
            }
        }

        if ok {
            count += 1;
        }

        i += 1;
    }

    count
}
