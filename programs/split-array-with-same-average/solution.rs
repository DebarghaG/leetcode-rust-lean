pub fn split_array_same_average(nums: &[i64]) -> bool {
    let n = nums.len();
    if n < 2 {
        return false;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total += nums[i];
        i += 1;
    }

    let max_k = n / 2;
    let n_i64 = n as i64;

    let mut max_sum: i64 = -1;
    let mut k: usize = 1;
    while k <= max_k {
        let prod = total * (k as i64);
        if prod % n_i64 == 0 {
            let target = prod / n_i64;
            if target > max_sum {
                max_sum = target;
            }
        }
        k += 1;
    }

    if max_sum < 0 {
        return false;
    }

    let max_sum_usize = max_sum as usize;
    let num_words = max_sum_usize / 31 + 1;
    let row_size = num_words;
    let total_size = (max_k + 1) * row_size;

    let mut dp: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < total_size {
        dp.push(0);
        j += 1;
    }

    dp[0] = 1;

    let mask: i64 = (1i64 << 31) - 1;

    let mut idx: usize = 0;
    while idx < n {
        let x = nums[idx];
        if x >= 0 && x <= max_sum {
            let x_usize = x as usize;
            let q = x_usize / 31;
            let r = x_usize % 31;

            let mut kk: usize = max_k;
            while kk >= 1 {
                let src_base = (kk - 1) * row_size;
                let dst_base = kk * row_size;

                let mut wi: usize = 0;
                while wi < row_size {
                    let w = dp[src_base + wi];
                    if w != 0 {
                        let shifted = w << r;
                        let dest = wi + q;

                        if dest < row_size {
                            let pos = dst_base + dest;
                            dp[pos] = dp[pos] | (shifted & mask);
                        }

                        let dest2 = dest + 1;
                        if dest2 < row_size {
                            let pos2 = dst_base + dest2;
                            dp[pos2] = dp[pos2] | (shifted >> 31);
                        }
                    }
                    wi += 1;
                }

                if kk == 1 {
                    break;
                }
                kk -= 1;
            }
        }
        idx += 1;
    }

    let mut kk: usize = 1;
    while kk <= max_k {
        let prod = total * (kk as i64);
        if prod % n_i64 == 0 {
            let target = prod / n_i64;
            if target >= 0 && target <= max_sum {
                let t = target as usize;
                let wi = t / 31;
                let bi = t % 31;

                if wi < row_size {
                    let base = kk * row_size;
                    let bitmask = 1i64 << bi;
                    if (dp[base + wi] & bitmask) != 0 {
                        return true;
                    }
                }
            }
        }
        kk += 1;
    }

    false
}
