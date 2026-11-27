pub fn find_length(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    let m = nums2.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k <= m {
        dp.push(0);
        k += 1;
    }

    let mut best: i64 = 0;
    let mut i: usize = 1;

    while i <= n {
        let mut j: usize = m;
        while j > 0 {
            if nums1[i - 1] == nums2[j - 1] {
                let value = dp[j - 1] + 1;
                dp[j] = value;
                if value > best {
                    best = value;
                }
            } else {
                dp[j] = 0;
            }
            j -= 1;
        }
        i += 1;
    }

    best
}
