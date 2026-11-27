pub fn minimum_moves(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(0);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    i = 0;
    while i < n {
        dp[i][i] = 1;
        i += 1;
    }

    let mut len = 2;
    while len <= n {
        let mut start = 0;
        while start + len <= n {
            let end = start + len - 1;
            let mut best: i64 = 1000000;

            if arr[start] == arr[end] {
                if len == 2 {
                    best = 1;
                } else {
                    best = dp[start + 1][end - 1];
                }
            }

            let mut k = start;
            while k < end {
                let candidate = dp[start][k] + dp[k + 1][end];
                if candidate < best {
                    best = candidate;
                }
                k += 1;
            }

            dp[start][end] = best;
            start += 1;
        }
        len += 1;
    }

    dp[0][n - 1]
}
