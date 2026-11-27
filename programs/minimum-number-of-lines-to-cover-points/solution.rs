pub fn minimum_lines(points: &[Vec<i64>]) -> i64 {
    let n = points.len();
    let total: usize = 1usize << n;

    let mut dp: Vec<i64> = Vec::new();
    let mut m: usize = 0;
    while m < total {
        dp.push(0);
        m += 1;
    }

    m = 1;
    while m < total {
        let mut best: i64 = 100;

        let mut i: usize = 0;
        while i < n {
            let bit_i: usize = 1usize << i;
            if (m & bit_i) != 0 {
                let mut j: usize = 0;
                while j < n {
                    let bit_j: usize = 1usize << j;
                    if (m & bit_j) != 0 {
                        let mut line: usize = 0;

                        if i == j {
                            line = bit_i;
                        } else {
                            let xi = points[i][0];
                            let yi = points[i][1];
                            let xj = points[j][0];
                            let yj = points[j][1];
                            let dx = xi - xj;
                            let dy = yi - yj;

                            let mut k: usize = 0;
                            while k < n {
                                let xk = points[k][0];
                                let yk = points[k][1];
                                if dx * (yk - yj) == dy * (xk - xj) {
                                    line = line + (1usize << k);
                                }
                                k += 1;
                            }
                        }

                        let covered = m & line;
                        let rem = m - covered;
                        let cand = 1 + dp[rem];
                        if cand < best {
                            best = cand;
                        }
                    }
                    j += 1;
                }
            }
            i += 1;
        }

        dp[m] = best;
        m += 1;
    }

    dp[total - 1]
}
