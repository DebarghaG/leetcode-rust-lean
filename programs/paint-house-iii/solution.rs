pub fn min_cost(houses: &[i64], cost: &[Vec<i64>], m: i64, n: i64, target: i64) -> i64 {
    // Top-level guards only (no returns inside loops).
    if m <= 0 || n <= 0 || target <= 0 {
        return -1;
    }
    let m_us = m as usize;
    let n_us = n as usize;
    let tgt = target as usize;

    if tgt > m_us || houses.len() < m_us || cost.len() < m_us {
        return -1;
    }

    // Validate inputs with a flag (still no returns inside loops).
    let mut ok = true;
    let mut k = 0;
    while k < m_us {
        if cost[k].len() < n_us {
            ok = false;
        }
        let hv = houses[k];
        if hv < 0 || hv > n {
            ok = false;
        }
        k += 1;
    }
    if !ok {
        return -1;
    }

    let inf: i64 = 1_000_000_000_000_000_000;

    // dp[t * n + c] = min cost after processed houses with t neighborhoods, last color c.
    // Build the initial dp (after house 0).
    let mut dp: Vec<i64> = Vec::new();

    // t = 0 row (unused, always inf)
    let mut c = 0;
    while c < n_us {
        dp.push(inf);
        c += 1;
    }
    // t = 1 row: cost of the first house under each color
    let h0 = houses[0];
    let mut c = 0;
    while c < n_us {
        if h0 == 0 {
            dp.push(cost[0][c]);
        } else if h0 == (c as i64 + 1) {
            dp.push(0);
        } else {
            dp.push(inf);
        }
        c += 1;
    }
    // t = 2..=tgt rows: inf
    let mut t = 2;
    while t <= tgt {
        let mut c = 0;
        while c < n_us {
            dp.push(inf);
            c += 1;
        }
        t += 1;
    }

    let mut i = 1;
    while i < m_us {
        let hi = houses[i];

        // Precompute, for each neighborhood count t, the two smallest dp[t][*] and the argmin.
        let mut b1: Vec<i64> = Vec::new();
        let mut b2: Vec<i64> = Vec::new();
        let mut arg1: Vec<usize> = Vec::new();
        let mut t = 0;
        while t <= tgt {
            let row = t * n_us;
            let mut m1 = inf;
            let mut m2 = inf;
            let mut a = n_us;
            let mut p = 0;
            while p < n_us {
                let v = dp[row + p];
                if v < m1 {
                    m2 = m1;
                    m1 = v;
                    a = p;
                } else if v < m2 {
                    m2 = v;
                }
                p += 1;
            }
            b1.push(m1);
            b2.push(m2);
            arg1.push(a);
            t += 1;
        }

        // Build next dp in flat order: row t=0 then rows t=1..=tgt.
        let mut next: Vec<i64> = Vec::new();
        let mut c = 0;
        while c < n_us {
            next.push(inf);
            c += 1;
        }

        let mut t = 1;
        while t <= tgt {
            let mut c = 0;
            while c < n_us {
                // Same color as previous house keeps neighborhood count t.
                let same = dp[t * n_us + c];

                // Different previous color bumps neighborhood count from t-1 to t.
                let mut diff = inf;
                if t >= 2 {
                    if arg1[t - 1] == c {
                        diff = b2[t - 1];
                    } else {
                        diff = b1[t - 1];
                    }
                }

                let mut best = same;
                if diff < best {
                    best = diff;
                }

                // Cost of using color (c+1) on house i, or inf if not allowed.
                let mut this_cost = inf;
                if hi == 0 {
                    this_cost = cost[i][c];
                } else if hi == (c as i64 + 1) {
                    this_cost = 0;
                }

                next.push(best + this_cost);
                c += 1;
            }
            t += 1;
        }

        dp = next;
        i += 1;
    }

    let base = tgt * n_us;
    let mut best = inf;
    let mut c = 0;
    while c < n_us {
        let v = dp[base + c];
        if v < best {
            best = v;
        }
        c += 1;
    }

    if best >= inf {
        -1
    } else {
        best
    }
}
