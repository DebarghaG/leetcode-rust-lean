pub fn count_substrings(s: &[u8], t: &[u8]) -> i64 {
    let n = s.len();
    let m = t.len();
    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < m {
            let mut k: usize = 0;
            let mut diff: i64 = 0;

            while i + k < n && j + k < m {
                if s[i + k] != t[j + k] {
                    diff += 1;
                }

                if diff == 1 {
                    ans += 1;
                } else if diff > 1 {
                    break;
                }

                k += 1;
            }

            j += 1;
        }
        i += 1;
    }

    ans
}
