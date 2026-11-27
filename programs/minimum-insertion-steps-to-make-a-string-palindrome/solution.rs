pub fn min_insertions(s: &[u8]) -> i64 {
    let n = s.len();
    if n <= 1 {
        return 0;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n {
            row.push(0);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    let mut len = 2usize;
    while len <= n {
        let mut start = 0usize;
        while start + len <= n {
            let end = start + len - 1;

            if s[start] == s[end] {
                if len == 2 {
                    dp[start][end] = 0;
                } else {
                    dp[start][end] = dp[start + 1][end - 1];
                }
            } else {
                let left = dp[start + 1][end];
                let right = dp[start][end - 1];
                if left < right {
                    dp[start][end] = left + 1;
                } else {
                    dp[start][end] = right + 1;
                }
            }

            start += 1;
        }
        len += 1;
    }

    dp[0][n - 1]
}
