pub fn assign_bikes(workers: &[Vec<i64>], bikes: &[Vec<i64>]) -> i64 {
    let n = workers.len();
    let m = bikes.len();

    let mut states: usize = 1;
    let mut k: usize = 0;
    while k < m {
        states = states * 2;
        k += 1;
    }

    let inf: i64 = 1_000_000_000;
    let total = (n + 1) * states;
    let mut dp: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < total {
        dp.push(inf);
        idx += 1;
    }

    dp[0] = 0;

    let mut i: usize = 0;
    while i < n {
        let mut mask: usize = 0;
        while mask < states {
            let cur = dp[i * states + mask];
            if cur < inf {
                let mut j: usize = 0;
                while j < m {
                    let used = (mask >> j) & 1;
                    if used == 0 {
                        let dx = if workers[i][0] > bikes[j][0] {
                            workers[i][0] - bikes[j][0]
                        } else {
                            bikes[j][0] - workers[i][0]
                        };

                        let dy = if workers[i][1] > bikes[j][1] {
                            workers[i][1] - bikes[j][1]
                        } else {
                            bikes[j][1] - workers[i][1]
                        };

                        let dist = dx + dy;
                        let next_mask = mask | (1usize << j);
                        let pos = (i + 1) * states + next_mask;
                        let cand = cur + dist;

                        if cand < dp[pos] {
                            dp[pos] = cand;
                        }
                    }
                    j += 1;
                }
            }
            mask += 1;
        }
        i += 1;
    }

    let mut ans = inf;
    let mut mask: usize = 0;
    while mask < states {
        let v = dp[n * states + mask];
        if v < ans {
            ans = v;
        }
        mask += 1;
    }

    ans
}
