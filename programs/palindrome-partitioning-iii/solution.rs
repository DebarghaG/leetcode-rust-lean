pub fn palindrome_partition(s: &[u8], k: i64) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let kk = k as usize;
    if kk >= n {
        return 0;
    }

    let total = n * n;
    let mut cost: Vec<i64> = Vec::new();
    let mut q = 0;
    while q < total {
        cost.push(0);
        q += 1;
    }

    let mut len = 2;
    while len <= n {
        let mut i = 0;
        while i + len <= n {
            let j = i + len - 1;
            let mut add: i64 = 0;
            if s[i] != s[j] {
                add = 1;
            }

            if len == 2 {
                cost[i * n + j] = add;
            } else {
                cost[i * n + j] = cost[(i + 1) * n + (j - 1)] + add;
            }

            i += 1;
        }
        len += 1;
    }

    let cols = n + 1;
    let dptotal = (kk + 1) * cols;
    let inf: i64 = 1000000000;

    let mut dp: Vec<i64> = Vec::new();
    q = 0;
    while q < dptotal {
        dp.push(inf);
        q += 1;
    }

    let mut i = 1;
    while i <= n {
        dp[cols + i] = cost[i - 1];
        i += 1;
    }

    let mut p = 2;
    while p <= kk {
        i = p;
        while i <= n {
            let mut best = inf;
            let mut t = p - 1;

            while t < i {
                let val = dp[(p - 1) * cols + t] + cost[t * n + (i - 1)];
                if val < best {
                    best = val;
                }
                t += 1;
            }

            dp[p * cols + i] = best;
            i += 1;
        }
        p += 1;
    }

    dp[kk * cols + n]
}
