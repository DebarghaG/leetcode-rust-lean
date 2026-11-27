fn update_dp(dp: &[i64], cost0: i64, add0: usize, cost1: i64, add1: usize) -> Vec<i64> {
    let inf: i64 = 1000000000000000000;
    let mut ndp: Vec<i64> = Vec::new();
    ndp.push(inf);
    ndp.push(inf);
    ndp.push(inf);
    ndp.push(inf);

    let mut r: usize = 0;
    while r < 4 {
        let cur = dp[r];
        if cur < inf {
            let val0 = cur + cost0;
            let mut t0 = r + add0;
            if t0 >= 4 {
                t0 = t0 - 4;
            }
            if val0 < ndp[t0] {
                ndp[t0] = val0;
            }

            let val1 = cur + cost1;
            let mut t1 = r + add1;
            if t1 >= 4 {
                t1 = t1 - 4;
            }
            if val1 < ndp[t1] {
                ndp[t1] = val1;
            }
        }
        r += 1;
    }

    ndp
}

pub fn min_flips(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let inf: i64 = 1000000000000000000;
    let mut dp: Vec<i64> = Vec::new();
    dp.push(0);
    dp.push(inf);
    dp.push(inf);
    dp.push(inf);

    let mut i: usize = 0;
    while i < m {
        let ri = m - 1 - i;
        let mut j: usize = 0;
        while j < n {
            let cj = n - 1 - j;

            if i <= ri && j <= cj {
                if i == ri && j == cj {
                    let b = grid[i][j];
                    let cost0 = b;
                    let cost1 = 1 - b;
                    dp = update_dp(&dp, cost0, 0, cost1, 1);
                } else if i == ri {
                    let a = grid[i][j];
                    let b = grid[i][cj];
                    let count = a + b;
                    let cost0 = count;
                    let cost1 = 2 - count;
                    dp = update_dp(&dp, cost0, 0, cost1, 2);
                } else if j == cj {
                    let a = grid[i][j];
                    let b = grid[ri][j];
                    let count = a + b;
                    let cost0 = count;
                    let cost1 = 2 - count;
                    dp = update_dp(&dp, cost0, 0, cost1, 2);
                } else {
                    let a = grid[i][j];
                    let b = grid[i][cj];
                    let c = grid[ri][j];
                    let d = grid[ri][cj];
                    let count = a + b + c + d;
                    let cost0 = count;
                    let cost1 = 4 - count;
                    dp = update_dp(&dp, cost0, 0, cost1, 0);
                }
            }

            j += 1;
        }
        i += 1;
    }

    dp[0]
}
