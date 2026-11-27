pub fn merge_stones(stones: &[i64], k: i64) -> i64 {
    let n = stones.len();

    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 0;
    }
    if k <= 1 {
        return -1;
    }

    let k_usize = k as usize;
    if k_usize < 2 {
        return -1;
    }

    let km1 = k_usize - 1;
    if (n - 1) % km1 != 0 {
        return -1;
    }

    let mut prefix: Vec<i64> = Vec::new();
    prefix.push(0);

    let mut i = 0;
    while i < n {
        let v = prefix[i] + stones[i];
        prefix.push(v);
        i += 1;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    i = 0;
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

    let inf: i64 = 1_000_000_000;

    let mut len = 2;
    while len <= n {
        let mut start = 0;
        while start + len <= n {
            let end = start + len - 1;
            let mut best = inf;
            let mut mid = start;

            while mid < end {
                let cand = dp[start][mid] + dp[mid + 1][end];
                if cand < best {
                    best = cand;
                }
                mid += km1;
            }

            if (len - 1) % km1 == 0 {
                if best != inf {
                    best += prefix[end + 1] - prefix[start];
                }
            }

            dp[start][end] = best;
            start += 1;
        }
        len += 1;
    }

    dp[0][n - 1]
}
