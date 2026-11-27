pub fn maximum_score(nums: &[i64], multipliers: &[i64]) -> i64 {
    let n: usize = nums.len();
    let m: usize = multipliers.len();

    if m == 0 {
        return 0;
    }

    let neg: i64 = -1000000000000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= m {
        dp.push(neg);
        k += 1;
    }
    dp[0] = 0;

    let mut i: usize = 0;
    while i < m {
        let mut ndp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k <= m {
            ndp.push(neg);
            k += 1;
        }

        let mut l: usize = 0;
        while l <= i {
            let base: i64 = dp[l];
            if base != neg {
                let left_value: i64 = nums[l];
                let left_candidate: i64 = base + multipliers[i] * left_value;
                if left_candidate > ndp[l + 1] {
                    ndp[l + 1] = left_candidate;
                }

                let right_index: usize = n - 1 - (i - l);
                let right_value: i64 = nums[right_index];
                let right_candidate: i64 = base + multipliers[i] * right_value;
                if right_candidate > ndp[l] {
                    ndp[l] = right_candidate;
                }
            }

            l += 1;
        }

        dp = ndp;
        i += 1;
    }

    let mut answer: i64 = neg;
    let mut l: usize = 0;
    while l <= m {
        if dp[l] > answer {
            answer = dp[l];
        }
        l += 1;
    }

    answer
}
