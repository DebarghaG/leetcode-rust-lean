pub fn max_value(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let kk = k as usize;
    let m_size: usize = 128;

    let total = (kk + 1) * m_size;

    let mut dp: Vec<bool> = Vec::new();
    let mut t = 0;
    while t < total {
        dp.push(false);
        t += 1;
    }
    dp[0] = true;

    let ltotal = (n + 1) * m_size;
    let mut left: Vec<bool> = Vec::new();
    t = 0;
    while t < ltotal {
        left.push(false);
        t += 1;
    }

    let dp_k_base = kk * m_size;
    let mut mask = 0;
    while mask < m_size {
        left[mask] = dp[dp_k_base + mask];
        mask += 1;
    }

    let mut idx = 0;
    while idx < n {
        let v = (nums[idx] as usize) & 127;

        let mut maxc = idx + 1;
        if maxc > kk {
            maxc = kk;
        }

        let mut c = maxc;
        while c > 0 {
            let src_base = (c - 1) * m_size;
            let dst_base = c * m_size;

            let mut mm = 0;
            while mm < m_size {
                if dp[src_base + mm] {
                    let nm = mm | v;
                    dp[dst_base + nm] = true;
                }
                mm += 1;
            }

            c -= 1;
        }

        let i_prefix = idx + 1;
        let out_base = i_prefix * m_size;
        let in_base = kk * m_size;

        mask = 0;
        while mask < m_size {
            left[out_base + mask] = dp[in_base + mask];
            mask += 1;
        }

        idx += 1;
    }

    let mut dp2: Vec<bool> = Vec::new();
    t = 0;
    while t < total {
        dp2.push(false);
        t += 1;
    }
    dp2[0] = true;

    let mut right: Vec<bool> = Vec::new();
    t = 0;
    while t < ltotal {
        right.push(false);
        t += 1;
    }

    mask = 0;
    while mask < m_size {
        right[n * m_size + mask] = dp2[dp_k_base + mask];
        mask += 1;
    }

    let mut idx2 = n;
    while idx2 > 0 {
        idx2 -= 1;
        let v2 = (nums[idx2] as usize) & 127;

        let processed = n - idx2;
        let mut maxc2 = processed;
        if maxc2 > kk {
            maxc2 = kk;
        }

        let mut c2 = maxc2;
        while c2 > 0 {
            let src_base2 = (c2 - 1) * m_size;
            let dst_base2 = c2 * m_size;

            let mut mm2 = 0;
            while mm2 < m_size {
                if dp2[src_base2 + mm2] {
                    let nm2 = mm2 | v2;
                    dp2[dst_base2 + nm2] = true;
                }
                mm2 += 1;
            }

            c2 -= 1;
        }

        let out_base2 = idx2 * m_size;
        let in_base2 = kk * m_size;

        mask = 0;
        while mask < m_size {
            right[out_base2 + mask] = dp2[in_base2 + mask];
            mask += 1;
        }
    }

    let mut ans: i64 = 0;
    let mut split = kk;
    while split + kk <= n {
        let left_base = split * m_size;
        let right_base = split * m_size;

        let mut a = 0;
        while a < m_size {
            if left[left_base + a] {
                let mut b = 0;
                while b < m_size {
                    if right[right_base + b] {
                        let val = (a ^ b) as i64;
                        if val > ans {
                            ans = val;
                        }
                    }
                    b += 1;
                }
            }
            a += 1;
        }

        split += 1;
    }

    ans
}
