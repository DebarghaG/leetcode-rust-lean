fn max_ops_for_score(nums: &[i64], score: i64) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let total = n * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dp.push(0);
        i += 1;
    }

    let mut len: usize = 2;
    while len <= n {
        let mut l: usize = 0;
        while l + len <= n {
            let r: usize = l + len - 1;
            let mut best: i64 = 0;

            if nums[l] + nums[l + 1] == score {
                let mut cand: i64 = 1;
                if l + 2 <= r {
                    cand += dp[(l + 2) * n + r];
                }
                if cand > best {
                    best = cand;
                }
            }

            if nums[r - 1] + nums[r] == score {
                let mut cand: i64 = 1;
                if r >= l + 2 {
                    cand += dp[l * n + (r - 2)];
                }
                if cand > best {
                    best = cand;
                }
            }

            if nums[l] + nums[r] == score {
                let mut cand: i64 = 1;
                if l + 2 <= r {
                    cand += dp[(l + 1) * n + (r - 1)];
                }
                if cand > best {
                    best = cand;
                }
            }

            dp[l * n + r] = best;
            l += 1;
        }
        len += 1;
    }

    dp[n - 1]
}

pub fn max_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let score1 = nums[0] + nums[1];
    let score2 = nums[n - 2] + nums[n - 1];
    let score3 = nums[0] + nums[n - 1];

    let mut ans = max_ops_for_score(nums, score1);
    let v2 = max_ops_for_score(nums, score2);
    if v2 > ans {
        ans = v2;
    }
    let v3 = max_ops_for_score(nums, score3);
    if v3 > ans {
        ans = v3;
    }

    ans
}
