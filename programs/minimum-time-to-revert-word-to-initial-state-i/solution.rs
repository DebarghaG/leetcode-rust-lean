pub fn minimum_time_to_initial_state(word: &[u8], k: i64) -> i64 {
    let n: i64 = word.len() as i64;
    let n_usize: usize = word.len();
    let mut t: i64 = 1;

    while t * k < n {
        let d: usize = (t * k) as usize;
        let m: usize = n_usize - d;
        let mut i: usize = 0;
        let mut ok: bool = true;

        while i < m {
            if word[d + i] != word[i] {
                ok = false;
            }
            i = i + 1;
        }

        if ok {
            return t;
        }

        t = t + 1;
    }

    t
}
