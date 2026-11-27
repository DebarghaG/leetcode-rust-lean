pub fn number_of_paths(grid: &[Vec<i64>], k: i64) -> i64 {
    if k <= 0 {
        return 0;
    }

    let m: usize = grid.len();
    if m == 0 {
        return 0;
    }

    let n: usize = grid[0].len();
    if n == 0 {
        return 0;
    }

    let modv: i64 = 1000000007;
    let kk: usize = k as usize;
    let total: usize = m * n * kk;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < total {
        dp.push(0);
        z = z + 1;
    }

    let mut i: usize = 0;
    while i < m {
        let mut j: usize = 0;
        while j < n {
            let base: usize = (i * n + j) * kk;
            let g: i64 = grid[i][j];
            let val: usize = (g % k) as usize;

            if i == 0 && j == 0 {
                dp[base + val] = 1;
            } else {
                let mut r: usize = 0;
                while r < kk {
                    let mut ways: i64 = 0;

                    if i > 0 {
                        let top_base: usize = ((i - 1) * n + j) * kk;
                        ways = ways + dp[top_base + r];
                    }

                    if j > 0 {
                        let left_base: usize = (i * n + (j - 1)) * kk;
                        ways = ways + dp[left_base + r];
                    }

                    if ways >= modv {
                        ways = ways - modv;
                    }

                    if ways != 0 {
                        let nr_i64: i64 = r as i64 + val as i64;
                        let nr: usize = if nr_i64 >= k {
                            (nr_i64 - k) as usize
                        } else {
                            nr_i64 as usize
                        };

                        let idx: usize = base + nr;
                        let mut nv: i64 = dp[idx] + ways;
                        if nv >= modv {
                            nv = nv - modv;
                        }
                        dp[idx] = nv;
                    }

                    r = r + 1;
                }
            }

            j = j + 1;
        }
        i = i + 1;
    }

    let target: usize = (m * n - 1) * kk;
    dp[target]
}
