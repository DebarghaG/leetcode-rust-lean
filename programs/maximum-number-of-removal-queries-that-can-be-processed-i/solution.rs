pub fn maximum_processable_queries(nums: &[i64], queries: &[i64]) -> i64 {
    let n = nums.len();
    let m = queries.len();
    if n == 0 || m == 0 {
        return 0;
    }

    // dp[i][j] = maximum number of queries processed when we have removed
    // i elements from the left end and j elements from the right end of nums.
    // The remaining candidate interval is [i, n - j).
    // Value -1 means the state is unreachable.
    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut a = 0;
    while a <= n {
        let mut row: Vec<i64> = Vec::new();
        let mut b = 0;
        while b <= n {
            row.push(-1);
            b += 1;
        }
        dp.push(row);
        a += 1;
    }

    dp[0][0] = 0;
    let mut ans: i64 = 0;

    // Process states in increasing order of i + j, since every transition
    // increases i + j by exactly one.
    let mut s = 0;
    while s <= n {
        let mut i = 0;
        while i <= s {
            let j = s - i;
            let k = dp[i][j];

            if k >= 0 {
                if k > ans {
                    ans = k;
                }

                // If the remaining interval is non-empty, we may consume or
                // drop an element from either end.
                if s < n {
                    let li = i;
                    let ri = n - 1 - j;

                    // Left side: consume nums[li] for the current query,
                    // or drop it (element excluded from the subsequence).
                    let mut nk = k;
                    if k < m as i64 {
                        let ki = k as usize;
                        if nums[li] >= queries[ki] {
                            nk = k + 1;
                        }
                    }
                    if nk > dp[i + 1][j] {
                        dp[i + 1][j] = nk;
                    }
                    if k > dp[i + 1][j] {
                        dp[i + 1][j] = k;
                    }

                    // Right side: consume nums[ri] for the current query,
                    // or drop it.
                    let mut nk2 = k;
                    if k < m as i64 {
                        let ki = k as usize;
                        if nums[ri] >= queries[ki] {
                            nk2 = k + 1;
                        }
                    }
                    if nk2 > dp[i][j + 1] {
                        dp[i][j + 1] = nk2;
                    }
                    if k > dp[i][j + 1] {
                        dp[i][j + 1] = k;
                    }
                }
            }

            i += 1;
        }
        s += 1;
    }

    ans
}
