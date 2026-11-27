pub fn connect_two_groups(cost: &[Vec<i64>]) -> i64 {
    let n: usize = cost.len();
    let m: usize = cost[0].len();
    let full: usize = 1usize << m;
    let inf: i64 = 1000000000;

    let mut dp: Vec<i64> = Vec::new();
    let mut s: usize = 0;
    while s < full {
        dp.push(inf);
        s += 1;
    }
    dp[0] = 0;

    let mut i: usize = 0;
    while i < n {
        let mut row_cost: Vec<i64> = Vec::new();
        s = 0;
        while s < full {
            row_cost.push(0);
            s += 1;
        }

        s = 1;
        while s < full {
            let mut sum: i64 = 0;
            let mut j: usize = 0;
            while j < m {
                if (s & (1usize << j)) != 0 {
                    sum += cost[i][j];
                }
                j += 1;
            }
            row_cost[s] = sum;
            s += 1;
        }

        let mut ndp: Vec<i64> = Vec::new();
        s = 0;
        while s < full {
            ndp.push(inf);
            s += 1;
        }

        let mut mask: usize = 0;
        while mask < full {
            let cur: i64 = dp[mask];
            if cur < inf {
                if mask != 0 {
                    let mut min_existing: i64 = inf;
                    let mut j: usize = 0;
                    while j < m {
                        if (mask & (1usize << j)) != 0 {
                            let c: i64 = cost[i][j];
                            if c < min_existing {
                                min_existing = c;
                            }
                        }
                        j += 1;
                    }
                    let val: i64 = cur + min_existing;
                    if val < ndp[mask] {
                        ndp[mask] = val;
                    }
                }

                let comp: usize = (full - 1usize) ^ mask;
                let mut sub: usize = comp;
                while sub > 0 {
                    let new_mask: usize = mask | sub;
                    let val: i64 = cur + row_cost[sub];
                    if val < ndp[new_mask] {
                        ndp[new_mask] = val;
                    }
                    sub = (sub - 1usize) & comp;
                }
            }
            mask += 1;
        }

        dp = ndp;
        i += 1;
    }

    dp[full - 1usize]
}
