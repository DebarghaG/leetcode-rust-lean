fn gcd_i64(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn valid_subarray_split(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return -1;
    }

    let inf: i64 = 1_000_000;
    let mut dp: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k <= n {
        dp.push(inf);
        k += 1;
    }

    dp[0] = 0;

    let mut i: usize = 0;
    while i < n {
        let mut best: i64 = inf;
        let mut j: usize = 0;

        while j <= i {
            if gcd_i64(nums[j], nums[i]) > 1 {
                let cand = dp[j] + 1;
                if cand < best {
                    best = cand;
                }
            }
            j += 1;
        }

        dp[i + 1] = best;
        i += 1;
    }

    if dp[n] >= inf {
        -1
    } else {
        dp[n]
    }
}
