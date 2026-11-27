pub fn repeated_substring_pattern(s: &[u8]) -> bool {
    let n: usize = s.len();
    if n <= 1 {
        return false;
    }

    let mut len: usize = 1;
    let half: usize = n / 2;

    while len <= half {
        if n % len == 0 {
            let mut ok: bool = true;
            let mut i: usize = len;

            while i < n {
                if s[i] != s[i - len] {
                    ok = false;
                    i = n;
                } else {
                    i += 1;
                }
            }

            if ok {
                return true;
            }
        }

        len += 1;
    }

    false
}
