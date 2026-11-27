pub fn minimum_xor_sum(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    if n == 0 {
        return 0;
    }

    let total = 1usize << n;
    let inf: i64 = 1i64 << 60;

    let mut dp: Vec<i64> = Vec::new();
    let mut k = 0usize;
    while k < total {
        dp.push(inf);
        k += 1;
    }
    dp[0] = 0;

    let mut mask = 0usize;
    while mask < total {
        if dp[mask] < inf {
            let i = popcount(mask);
            if i < n {
                let mut j = 0usize;
                while j < n {
                    let bit = 1usize << j;
                    if (mask & bit) == 0 {
                        let next_mask = mask | bit;
                        let candidate = dp[mask] + (nums1[i] ^ nums2[j]);
                        if candidate < dp[next_mask] {
                            dp[next_mask] = candidate;
                        }
                    }
                    j += 1;
                }
            }
        }
        mask += 1;
    }

    dp[total - 1]
}

fn popcount(mut x: usize) -> usize {
    let mut count = 0usize;
    while x > 0 {
        count += x % 2;
        x = x / 2;
    }
    count
}
