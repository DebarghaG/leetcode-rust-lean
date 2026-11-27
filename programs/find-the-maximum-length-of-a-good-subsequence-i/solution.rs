pub fn maximum_length(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut kcap = k;
    let max_changes = n as i64 - 1;
    if kcap > max_changes {
        kcap = max_changes;
    }
    if kcap < 0 {
        kcap = 0;
    }

    let cols = (kcap + 1) as usize;
    let total = n * cols;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < total {
        dp.push(0);
        z += 1;
    }

    let mut ans: i64 = 1;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = 0;

        while j < cols {
            let mut best: i64 = 1;
            let mut p: usize = 0;

            while p < i {
                let base = p * cols;
                let mut cand: i64 = 0;

                if nums[p] == nums[i] {
                    cand = dp[base + j] + 1;
                } else {
                    if j > 0 {
                        cand = dp[base + j - 1] + 1;
                    }
                }

                if cand > best {
                    best = cand;
                }

                p += 1;
            }

            dp[i * cols + j] = best;

            if best > ans {
                ans = best;
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
