pub fn has_special_substring(s: &[u8], k: i64) -> bool {
    let n = s.len();
    if n == 0 {
        return false;
    }

    let mut run_len: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if s[i] == s[i - 1] {
            run_len += 1;
        } else {
            if run_len == k {
                return true;
            }
            run_len = 1;
        }
        i += 1;
    }

    run_len == k
}
