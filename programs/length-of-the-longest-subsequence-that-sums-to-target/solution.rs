pub fn length_of_longest_subsequence(nums: &[i64], target: i64) -> i64 {
    if target < 0 {
        return -1;
    }

    let t: usize = target as usize;
    let mut dp: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i <= t {
        dp.push(-1);
        i += 1;
    }

    dp[0] = 0;

    let n = nums.len();
    let mut idx: usize = 0;

    while idx < n {
        let x = nums[idx];

        if x > 0 && x <= target {
            let xu: usize = x as usize;
            let mut s: usize = t;

            while s >= xu {
                let prev = dp[s - xu];
                if prev >= 0 {
                    let candidate = prev + 1;
                    if candidate > dp[s] {
                        dp[s] = candidate;
                    }
                }

                if s == xu {
                    break;
                }
                s -= 1;
            }
        }

        idx += 1;
    }

    dp[t]
}
