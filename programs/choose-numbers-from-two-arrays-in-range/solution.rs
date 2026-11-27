const MOD: i64 = 1_000_000_007;

fn add_mod(a: i64, b: i64) -> i64 {
    let s = a + b;
    if s >= MOD {
        s - MOD
    } else {
        s
    }
}

pub fn count_subranges(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();

    let mut dp: Vec<i64> = Vec::new();
    dp.push(1);

    let mut zero_idx: usize = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let a = nums1[i];
        let b = nums2[i];
        let add_len = (a + b) as usize;
        let old_len = dp.len();

        let mut t: usize = 0;
        while t < add_len {
            dp.push(0);
            t += 1;
        }

        let mut k: usize = old_len;
        while k > 0 {
            k -= 1;
            let c = dp[k];
            if c != 0 {
                let idx = k + add_len;
                let cur = dp[idx];
                dp[idx] = add_mod(cur, c);
            }
        }

        zero_idx += b as usize;
        ans = add_mod(ans, dp[zero_idx]);

        let cur0 = dp[zero_idx];
        dp[zero_idx] = add_mod(cur0, 1);

        i += 1;
    }

    ans
}
