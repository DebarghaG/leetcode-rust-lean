pub fn maximum_strength(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let kk = k as usize;
    let neg: i64 = -4_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut ongoing: Vec<i64> = Vec::new();

    let mut t = 0usize;
    while t <= kk {
        dp.push(neg);
        ongoing.push(neg);
        t += 1;
    }
    dp[0] = 0;

    let mut i = 0usize;
    while i < n {
        let x = nums[i];
        let mut j = kk;

        while j > 0 {
            let jj = j as i64;
            let mag = k - jj + 1;
            let coeff: i64 = if j % 2 == 1 { mag } else { -mag };
            let add = coeff * x;

            let mut best = neg;

            if ongoing[j] != neg {
                let extend = ongoing[j] + add;
                if extend > best {
                    best = extend;
                }
            }

            if dp[j - 1] != neg {
                let start = dp[j - 1] + add;
                if start > best {
                    best = start;
                }
            }

            ongoing[j] = best;
            if best > dp[j] {
                dp[j] = best;
            }

            j -= 1;
        }

        i += 1;
    }

    dp[kk]
}
