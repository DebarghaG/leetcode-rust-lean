pub fn mct_from_leaf_values(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n <= 1 {
        return 0;
    }

    let size = n * n;
    let mut dp: Vec<i64> = Vec::new();
    let mut t = 0;
    while t < size {
        dp.push(0);
        t += 1;
    }

    let mut len = 2;
    while len <= n {
        let mut i = 0;
        while i + len <= n {
            let j = i + len - 1;
            let mut best: i64 = 1_000_000_000;

            let mut k = i;
            while k < j {
                let mut max_left = 0;
                let mut p = i;
                while p <= k {
                    if arr[p] > max_left {
                        max_left = arr[p];
                    }
                    p += 1;
                }

                let mut max_right = 0;
                let mut q = k + 1;
                while q <= j {
                    if arr[q] > max_right {
                        max_right = arr[q];
                    }
                    q += 1;
                }

                let left = dp[i * n + k];
                let right = dp[(k + 1) * n + j];
                let cand = left + right + max_left * max_right;

                if cand < best {
                    best = cand;
                }

                k += 1;
            }

            dp[i * n + j] = best;
            i += 1;
        }
        len += 1;
    }

    dp[n - 1]
}
