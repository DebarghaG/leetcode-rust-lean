pub fn is_match(s: &[u8], p: &[u8]) -> bool {
    let n: usize = s.len();
    let m: usize = p.len();
    let cols: usize = m + 1;
    let total: usize = (n + 1) * cols;

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < total {
        dp.push(0);
        k += 1;
    }

    dp[0] = 1;

    let mut j: usize = 1;
    while j <= m {
        if j >= 2 && p[j - 1] == b'*' {
            dp[j] = dp[j - 2];
        }
        j += 1;
    }

    let mut i: usize = 1;
    while i <= n {
        j = 1;
        while j <= m {
            let cur: usize = i * cols + j;

            if j >= 2 && p[j - 1] == b'*' {
                let zero: i64 = dp[i * cols + (j - 2)];
                let mut one: i64 = 0;

                if p[j - 2] == b'.' || p[j - 2] == s[i - 1] {
                    one = dp[(i - 1) * cols + j];
                }

                if zero != 0 || one != 0 {
                    dp[cur] = 1;
                } else {
                    dp[cur] = 0;
                }
            } else {
                if p[j - 1] == b'.' || p[j - 1] == s[i - 1] {
                    dp[cur] = dp[(i - 1) * cols + (j - 1)];
                } else {
                    dp[cur] = 0;
                }
            }

            j += 1;
        }
        i += 1;
    }

    dp[n * cols + m] != 0
}
