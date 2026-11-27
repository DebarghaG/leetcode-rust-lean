pub fn longest_palindrome(s: &[u8], t: &[u8]) -> i64 {
    let n = s.len();
    let m = t.len();
    let mut best: i64 = 1;

    let mut s0 = 0usize;
    while s0 <= n {
        let mut s1 = s0;
        while s1 <= n {
            let mut t0 = 0usize;
            while t0 <= m {
                let mut t1 = t0;
                while t1 <= m {
                    let len = (s1 - s0) + (t1 - t0);
                    if len as i64 > best
                        && is_palindrome_combined(s, s0, s1, t, t0, t1)
                    {
                        best = len as i64;
                    }
                    t1 += 1;
                }
                t0 += 1;
            }
            s1 += 1;
        }
        s0 += 1;
    }

    best
}

fn combined_get(
    s: &[u8],
    s0: usize,
    s1: usize,
    t: &[u8],
    t0: usize,
    t1: usize,
    idx: usize,
) -> u8 {
    let s_len = s1 - s0;
    if idx < s_len {
        s[s0 + idx]
    } else {
        t[t0 + (idx - s_len)]
    }
}

fn is_palindrome_combined(
    s: &[u8],
    s0: usize,
    s1: usize,
    t: &[u8],
    t0: usize,
    t1: usize,
) -> bool {
    let len = (s1 - s0) + (t1 - t0);
    if len <= 1 {
        return true;
    }

    let mut left = 0usize;
    let mut right = len - 1usize;

    while left < right {
        let a = combined_get(s, s0, s1, t, t0, t1, left);
        let b = combined_get(s, s0, s1, t, t0, t1, right);
        if a != b {
            return false;
        }
        left += 1;
        right -= 1;
    }

    true
}
