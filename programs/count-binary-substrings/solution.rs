pub fn count_binary_substrings(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut ans: i64 = 0;
    let mut prev: i64 = 0;
    let mut cur: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if s[i] == s[i - 1] {
            cur += 1;
        } else {
            if prev < cur {
                ans += prev;
            } else {
                ans += cur;
            }
            prev = cur;
            cur = 1;
        }
        i += 1;
    }

    if prev < cur {
        ans += prev;
    } else {
        ans += cur;
    }

    ans
}
