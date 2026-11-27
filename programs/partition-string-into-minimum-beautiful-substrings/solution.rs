fn is_beautiful(s: &[u8], start: usize, end: usize) -> bool {
    if start >= end {
        return false;
    }
    if s[start] == b'0' {
        return false;
    }

    let mut val: i64 = 0;
    let mut k: usize = start;
    while k < end {
        val = val * 2;
        if s[k] == b'1' {
            val = val + 1;
        }
        k += 1;
    }

    if val < 1 {
        return false;
    }

    while val > 1 {
        if val % 5 != 0 {
            return false;
        }
        val = val / 5;
    }

    true
}

pub fn minimum_beautiful_substrings(s: &[u8]) -> i64 {
    let n: usize = s.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        dp.push(1000000);
        i += 1;
    }

    dp[0] = 0;

    i = 0;
    while i < n {
        if dp[i] < 1000000 {
            let mut j: usize = i + 1;
            while j <= n {
                if is_beautiful(s, i, j) {
                    let cand: i64 = dp[i] + 1;
                    if cand < dp[j] {
                        dp[j] = cand;
                    }
                }
                j += 1;
            }
        }
        i += 1;
    }

    if dp[n] >= 1000000 {
        -1
    } else {
        dp[n]
    }
}
