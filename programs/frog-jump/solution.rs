pub fn can_cross(stones: &[i64]) -> bool {
    let n = stones.len();
    if n == 0 {
        return false;
    }
    if n == 1 {
        return true;
    }
    if stones[1] != 1 {
        return false;
    }

    let width = n + 1;
    let total = n * width;
    let mut dp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < total {
        dp.push(0);
        t += 1;
    }

    // dp[i * width + k] == 1 means stone i is reachable with last jump length k.
    // For the initial stone 0, we use k = 0 so the first jump can be 1.
    dp[0] = 1;

    let mut i: usize = 1;
    while i < n {
        let mut j: usize = 0;
        while j < i {
            let d: i64 = stones[i] - stones[j];
            if d > 0 && d <= n as i64 {
                let du: usize = d as usize;
                let base_j: usize = j * width;
                let mut ok: bool = false;

                if du >= 1 {
                    let k0: usize = du - 1;
                    if k0 <= n && dp[base_j + k0] == 1 {
                        ok = true;
                    }
                }
                if !ok {
                    let k1: usize = du;
                    if k1 <= n && dp[base_j + k1] == 1 {
                        ok = true;
                    }
                }
                if !ok {
                    let k2: usize = du + 1;
                    if k2 <= n && dp[base_j + k2] == 1 {
                        ok = true;
                    }
                }

                if ok {
                    dp[i * width + du] = 1;
                }
            }
            j += 1;
        }
        i += 1;
    }

    let base: usize = (n - 1) * width;
    let mut k: usize = 0;
    while k <= n {
        if dp[base + k] == 1 {
            return true;
        }
        k += 1;
    }

    false
}
