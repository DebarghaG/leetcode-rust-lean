pub fn min_cost(maxTime: i64, edges: &[Vec<i64>], passingFees: &[i64]) -> i64 {
    let n = passingFees.len();
    let tmax = maxTime as usize;
    let inf: i64 = 1_000_000_000;

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j <= tmax {
            row.push(inf);
            j += 1;
        }
        dp.push(row);
        i += 1;
    }

    dp[0][0] = passingFees[0];

    let m = edges.len();
    let mut t = 0;
    while t <= tmax {
        let mut e = 0;
        while e < m {
            let x = edges[e][0] as usize;
            let y = edges[e][1] as usize;
            let w = edges[e][2] as usize;
            let tw = t + w;

            if tw <= tmax {
                let cost_x = dp[x][t];
                if cost_x < inf {
                    let next_cost = cost_x + passingFees[y];
                    if next_cost < dp[y][tw] {
                        dp[y][tw] = next_cost;
                    }
                }

                let cost_y = dp[y][t];
                if cost_y < inf {
                    let next_cost = cost_y + passingFees[x];
                    if next_cost < dp[x][tw] {
                        dp[x][tw] = next_cost;
                    }
                }
            }

            e += 1;
        }
        t += 1;
    }

    let dest = n - 1;
    let mut ans = inf;
    let mut tt = 0;
    while tt <= tmax {
        let c = dp[dest][tt];
        if c < ans {
            ans = c;
        }
        tt += 1;
    }

    if ans == inf {
        -1
    } else {
        ans
    }
}
