fn popcount(mut x: usize) -> usize {
    let mut count: usize = 0;
    while x > 0 {
        count += x & 1;
        x = x >> 1;
    }
    count
}

pub fn maximum_cost(n: i64, highways: &[Vec<i64>], k: i64) -> i64 {
    if k < 0 {
        return -1;
    }
    if k >= n {
        return -1;
    }

    let n_us = n as usize;
    let states = 1usize << n_us;

    let mut w: Vec<i64> = Vec::new();
    let total_w = n_us * n_us;
    let mut i = 0usize;
    while i < total_w {
        w.push(-1);
        i += 1;
    }

    let mut e = 0usize;
    while e < highways.len() {
        let a = highways[e][0] as usize;
        let b = highways[e][1] as usize;
        let t = highways[e][2];
        w[a * n_us + b] = t;
        w[b * n_us + a] = t;
        e += 1;
    }

    let total = states * n_us;
    let mut dp: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < total {
        dp.push(-1);
        j += 1;
    }

    let mut v0 = 0usize;
    while v0 < n_us {
        let mask = 1usize << v0;
        dp[mask * n_us + v0] = 0;
        v0 += 1;
    }

    let mut mask = 1usize;
    while mask < states {
        let mut v = 0usize;
        while v < n_us {
            let cur = dp[mask * n_us + v];
            if cur >= 0 {
                let mut u = 0usize;
                while u < n_us {
                    let weight = w[v * n_us + u];
                    if weight >= 0 {
                        let bit = 1usize << u;
                        if (mask & bit) == 0 {
                            let nmask = mask | bit;
                            let cand = cur + weight;
                            let nidx = nmask * n_us + u;
                            if cand > dp[nidx] {
                                dp[nidx] = cand;
                            }
                        }
                    }
                    u += 1;
                }
            }
            v += 1;
        }
        mask += 1;
    }

    let target = (k as usize) + 1;
    let mut ans: i64 = -1;
    let mut m = 0usize;
    while m < states {
        if popcount(m) == target {
            let mut v = 0usize;
            while v < n_us {
                let val = dp[m * n_us + v];
                if val > ans {
                    ans = val;
                }
                v += 1;
            }
        }
        m += 1;
    }

    ans
}
