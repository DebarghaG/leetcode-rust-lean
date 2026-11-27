pub fn max_dot_product(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    let m = nums2.len();
    let cols = m + 1;
    let neg_inf: i64 = -1000000000000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i <= n {
        let mut j: usize = 0;
        while j <= m {
            dp.push(neg_inf);
            j += 1;
        }
        i += 1;
    }

    i = 1;
    while i <= n {
        let mut j: usize = 1;
        while j <= m {
            let mut best = dp[(i - 1) * cols + j];

            let from_left = dp[i * cols + (j - 1)];
            if from_left > best {
                best = from_left;
            }

            let prev = dp[(i - 1) * cols + (j - 1)];
            let mut add: i64 = 0;
            if prev > 0 {
                add = prev;
            }

            let candidate = nums1[i - 1] * nums2[j - 1] + add;
            if candidate > best {
                best = candidate;
            }

            dp[i * cols + j] = best;
            j += 1;
        }
        i += 1;
    }

    dp[n * cols + m]
}
