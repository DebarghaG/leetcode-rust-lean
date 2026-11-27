pub fn minimum_operations(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return 0;
    }

    let n = grid[0].len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<i64> = Vec::new();

    let mut v: usize = 0;
    while v < 10 {
        let val = v as i64;
        let mut cost: i64 = 0;
        let mut i: usize = 0;

        while i < m {
            if grid[i][0] != val {
                cost += 1;
            }
            i += 1;
        }

        dp.push(cost);
        v += 1;
    }

    let mut j: usize = 1;
    while j < n {
        let mut next_dp: Vec<i64> = Vec::new();
        let mut vv: usize = 0;

        while vv < 10 {
            let val = vv as i64;
            let mut cost: i64 = 0;
            let mut i: usize = 0;

            while i < m {
                if grid[i][j] != val {
                    cost += 1;
                }
                i += 1;
            }

            let mut best: i64 = 0;
            let mut found = false;
            let mut u: usize = 0;

            while u < 10 {
                if u != vv {
                    if !found || dp[u] < best {
                        best = dp[u];
                        found = true;
                    }
                }
                u += 1;
            }

            next_dp.push(cost + best);
            vv += 1;
        }

        dp = next_dp;
        j += 1;
    }

    let mut answer = dp[0];
    let mut k: usize = 1;

    while k < 10 {
        if dp[k] < answer {
            answer = dp[k];
        }
        k += 1;
    }

    answer
}
