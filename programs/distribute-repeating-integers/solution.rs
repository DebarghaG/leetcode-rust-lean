pub fn can_distribute(nums: &[i64], quantity: &[i64]) -> bool {
    let m = quantity.len();

    let mut total: usize = 1;
    let mut i: usize = 0;
    while i < m {
        total = total * 2;
        i += 1;
    }

    let mut total_quantity: i64 = 0;
    i = 0;
    while i < m {
        total_quantity += quantity[i];
        i += 1;
    }
    if total_quantity > nums.len() as i64 {
        return false;
    }

    let mut values: Vec<i64> = Vec::new();
    let mut freq: Vec<i64> = Vec::new();

    i = 0;
    while i < nums.len() {
        let x = nums[i];
        let mut found = false;
        let mut j = 0usize;
        while j < values.len() {
            if values[j] == x {
                freq[j] = freq[j] + 1;
                found = true;
            }
            j += 1;
        }
        if !found {
            values.push(x);
            freq.push(1);
        }
        i += 1;
    }

    let mut subset_sum: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        subset_sum.push(0);
        i += 1;
    }

    let mut mask = 1usize;
    while mask < total {
        let mut sum: i64 = 0;
        let mut b = 0usize;
        while b < m {
            if (mask & (1usize << b)) != 0 {
                sum += quantity[b];
            }
            b += 1;
        }
        subset_sum[mask] = sum;
        mask += 1;
    }

    let mut dp: Vec<bool> = Vec::new();
    i = 0;
    while i < total {
        dp.push(false);
        i += 1;
    }
    dp[0] = true;

    let full = total - 1;

    let mut f = 0usize;
    while f < freq.len() {
        let capacity = freq[f];

        let mut next_dp: Vec<bool> = Vec::new();
        let mut k = 0usize;
        while k < total {
            next_dp.push(dp[k]);
            k += 1;
        }

        let mut covered = 0usize;
        while covered < total {
            if dp[covered] {
                let remaining = full - covered;
                let mut sub = remaining;
                while sub > 0 {
                    if subset_sum[sub] <= capacity {
                        next_dp[covered | sub] = true;
                    }
                    sub = (sub - 1) & remaining;
                }
            }
            covered += 1;
        }

        k = 0;
        while k < total {
            dp[k] = next_dp[k];
            k += 1;
        }

        if dp[full] {
            return true;
        }

        f += 1;
    }

    dp[full]
}
