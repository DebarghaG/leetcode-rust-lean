pub fn cherry_pickup(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }
    if grid[0][0] == -1 || grid[n - 1][n - 1] == -1 {
        return 0;
    }
    if n == 1 {
        return grid[0][0];
    }

    let neg: i64 = -1000000000;
    let size = n * n;

    let mut prev: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < size {
        prev.push(neg);
        i += 1;
    }
    prev[0] = grid[0][0];

    let steps = 2 * n - 2;
    let mut t = 1;

    while t <= steps {
        let mut cur: Vec<i64> = Vec::new();
        let mut z = 0;
        while z < size {
            cur.push(neg);
            z += 1;
        }

        let lo = if t > n - 1 { t - (n - 1) } else { 0 };
        let hi = if t < n { t } else { n - 1 };

        let mut r1 = lo;
        while r1 <= hi {
            let c1 = t - r1;

            let mut r2 = lo;
            while r2 <= hi {
                let c2 = t - r2;

                if grid[r1][c1] != -1 && grid[r2][c2] != -1 {
                    let idx = r1 * n + r2;
                    let mut best = neg;

                    let v00 = prev[idx];
                    if v00 > best {
                        best = v00;
                    }

                    if r2 > 0 {
                        let v01 = prev[r1 * n + (r2 - 1)];
                        if v01 > best {
                            best = v01;
                        }
                    }

                    if r1 > 0 {
                        let v10 = prev[(r1 - 1) * n + r2];
                        if v10 > best {
                            best = v10;
                        }
                    }

                    if r1 > 0 && r2 > 0 {
                        let v11 = prev[(r1 - 1) * n + (r2 - 1)];
                        if v11 > best {
                            best = v11;
                        }
                    }

                    if best != neg {
                        let mut gain = grid[r1][c1];
                        if r1 != r2 || c1 != c2 {
                            gain += grid[r2][c2];
                        }
                        cur[idx] = best + gain;
                    }
                }

                r2 += 1;
            }

            r1 += 1;
        }

        prev = cur;
        t += 1;
    }

    let ans = prev[(n - 1) * n + (n - 1)];
    if ans < 0 {
        0
    } else {
        ans
    }
}
