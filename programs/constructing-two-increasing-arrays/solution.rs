pub fn min_largest(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n1: usize = nums1.len();
    let n2: usize = nums2.len();
    let stride: usize = n2 + 1;
    let total: usize = (n1 + 1) * stride * 2;
    let inf: i64 = 1_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < total {
        dp.push(inf);
        z += 1;
    }

    dp[0] = 0;

    let mut i: usize = 0;
    while i <= n1 {
        let mut j: usize = 0;
        while j <= n2 {
            let base: usize = (i * stride + j) * 2;

            let mut p: usize = 0;
            while p < 2 {
                let val: i64 = dp[base + p];

                if val < inf {
                    if i < n1 {
                        let b: i64 = nums1[i];
                        let same: bool = (b == 0 && p == 0) || (b == 1 && p == 1);
                        let cost: i64 = if same { 2 } else { 1 };
                        let np: usize = if b == 0 { 0 } else { 1 };
                        let target: usize = ((i + 1) * stride + j) * 2 + np;
                        let cand: i64 = val + cost;

                        if cand < dp[target] {
                            dp[target] = cand;
                        }
                    }

                    if j < n2 {
                        let b: i64 = nums2[j];
                        let same: bool = (b == 0 && p == 0) || (b == 1 && p == 1);
                        let cost: i64 = if same { 2 } else { 1 };
                        let np: usize = if b == 0 { 0 } else { 1 };
                        let target: usize = (i * stride + (j + 1)) * 2 + np;
                        let cand: i64 = val + cost;

                        if cand < dp[target] {
                            dp[target] = cand;
                        }
                    }
                }

                p += 1;
            }

            j += 1;
        }

        i += 1;
    }

    let final_base: usize = (n1 * stride + n2) * 2;
    let a: i64 = dp[final_base];
    let b: i64 = dp[final_base + 1];

    if a < b { a } else { b }
}
