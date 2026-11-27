pub fn min_skips(dist: &[i64], speed: i64, hoursBefore: i64) -> i64 {
    let n = dist.len();
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i <= n {
        dp.push(inf);
        i += 1;
    }
    dp[0] = 0;

    let mut road = 0;
    while road < n {
        let mut ndp: Vec<i64> = Vec::new();
        let mut k = 0;
        while k <= n {
            ndp.push(inf);
            k += 1;
        }

        let mut skips = 0;
        while skips <= road {
            if dp[skips] < inf {
                let base = dp[skips] + dist[road];

                if road == n - 1 {
                    if base < ndp[skips] {
                        ndp[skips] = base;
                    }
                } else {
                    let rem = base % speed;
                    let mut rested = base;
                    if rem != 0 {
                        rested = base + (speed - rem);
                    }

                    if rested < ndp[skips] {
                        ndp[skips] = rested;
                    }

                    if base < ndp[skips + 1] {
                        ndp[skips + 1] = base;
                    }
                }
            }
            skips += 1;
        }

        dp = ndp;
        road += 1;
    }

    let limit = hoursBefore * speed;
    let mut skips = 0;
    let mut answer: i64 = 0;
    while skips <= n {
        if dp[skips] <= limit {
            return answer;
        }
        skips += 1;
        answer += 1;
    }

    -1
}
