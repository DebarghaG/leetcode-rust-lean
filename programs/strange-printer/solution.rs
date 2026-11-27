pub fn strange_printer(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let total = n * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < total {
        dp.push(0);
        t += 1;
    }

    let mut i: usize = 0;
    while i < n {
        dp[i * n + i] = 1;
        i += 1;
    }

    let mut len: usize = 2;
    while len <= n {
        let mut start: usize = 0;
        while start + len <= n {
            let end = start + len - 1;

            let mut best = dp[(start + 1) * n + end] + 1;
            let mut k = start + 1;

            while k <= end {
                if s[k] == s[start] {
                    let left = if k == start + 1 {
                        0
                    } else {
                        dp[(start + 1) * n + (k - 1)]
                    };

                    let value = left + dp[k * n + end];
                    if value < best {
                        best = value;
                    }
                }
                k += 1;
            }

            dp[start * n + end] = best;
            start += 1;
        }
        len += 1;
    }

    dp[n - 1]
}
