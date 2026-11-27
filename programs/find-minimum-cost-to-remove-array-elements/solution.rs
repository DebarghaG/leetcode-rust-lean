fn max_i64(a: i64, b: i64) -> i64 {
    if a > b {
        a
    } else {
        b
    }
}

pub fn min_cost(nums: &[i64]) -> i64 {
    let n = nums.len();

    if n == 0 {
        return 0;
    }
    if n == 1 {
        return nums[0];
    }
    if n == 2 {
        return max_i64(nums[0], nums[1]);
    }

    let inf: i64 = 1000000000000000000;

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut r: usize = 0;
    while r <= n {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < n {
            row.push(inf);
            c += 1;
        }
        dp.push(row);
        r += 1;
    }

    // First operation: choose any two of nums[0], nums[1], nums[2]
    // to remove, leaving one of them as the current leftover.
    let mut k: usize = 0;
    while k < 3 {
        let mut cost: i64 = 0;

        if k == 0 {
            cost = max_i64(nums[1], nums[2]);
        } else if k == 1 {
            cost = max_i64(nums[0], nums[2]);
        } else {
            cost = max_i64(nums[0], nums[1]);
        }

        if cost < dp[3][k] {
            dp[3][k] = cost;
        }

        k += 1;
    }

    let mut p: usize = 3;

    // State: dp[p][j] = minimum cost when the next unprocessed index is p
    // and the single leftover element before it is nums[j].
    while p + 1 < n {
        let mut j: usize = 0;

        while j < n {
            let cur = dp[p][j];

            if cur < inf {
                // Keep nums[j] as the leftover, remove nums[p] and nums[p + 1].
                let add0 = max_i64(nums[p], nums[p + 1]);
                let val0 = cur + add0;
                if val0 < dp[p + 2][j] {
                    dp[p + 2][j] = val0;
                }

                // Keep nums[p] as the leftover, remove nums[j] and nums[p + 1].
                let add1 = max_i64(nums[j], nums[p + 1]);
                let val1 = cur + add1;
                if val1 < dp[p + 2][p] {
                    dp[p + 2][p] = val1;
                }

                // Keep nums[p + 1] as the leftover, remove nums[j] and nums[p].
                let add2 = max_i64(nums[j], nums[p]);
                let val2 = cur + add2;
                if val2 < dp[p + 2][p + 1] {
                    dp[p + 2][p + 1] = val2;
                }
            }

            j += 1;
        }

        p += 2;
    }

    let mut ans: i64 = inf;

    if p == n {
        // Only the leftover element remains.
        let mut j: usize = 0;
        while j < n {
            let cur = dp[p][j];
            if cur < inf {
                let total = cur + nums[j];
                if total < ans {
                    ans = total;
                }
            }
            j += 1;
        }
    } else {
        // p == n - 1: the leftover element and nums[n - 1] remain.
        let mut j: usize = 0;
        while j < n {
            let cur = dp[p][j];
            if cur < inf {
                let total = cur + max_i64(nums[j], nums[n - 1]);
                if total < ans {
                    ans = total;
                }
            }
            j += 1;
        }
    }

    ans
}
