pub fn cherry_pickup(grid: &[Vec<i64>]) -> i64 {
    let rows = grid.len();
    let cols = grid[0].len();
    let neg: i64 = -1000000000;
    let size = cols * cols;

    let mut dp: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z < size {
        dp.push(neg);
        z += 1;
    }

    let last = cols - 1;
    let mut initial = grid[0][0];
    if last != 0 {
        initial += grid[0][last];
    }
    dp[last] = initial;

    let mut i = 1usize;
    while i < rows {
        let row = &grid[i];
        let mut next: Vec<i64> = Vec::new();
        let mut zz = 0usize;
        while zz < size {
            next.push(neg);
            zz += 1;
        }

        let mut q1 = 0usize;
        while q1 < cols {
            let mut q2 = 0usize;
            while q2 < cols {
                let base = dp[q1 * cols + q2];
                if base != neg {
                    let s1 = if q1 == 0 { 0 } else { q1 - 1 };
                    let e1 = if q1 + 1 < cols { q1 + 1 } else { q1 };
                    let s2 = if q2 == 0 { 0 } else { q2 - 1 };
                    let e2 = if q2 + 1 < cols { q2 + 1 } else { q2 };

                    let mut r1 = s1;
                    while r1 <= e1 {
                        let mut r2 = s2;
                        while r2 <= e2 {
                            let mut add = row[r1];
                            if r1 != r2 {
                                add += row[r2];
                            }

                            let cand = base + add;
                            let idx = r1 * cols + r2;
                            if cand > next[idx] {
                                next[idx] = cand;
                            }

                            r2 += 1;
                        }
                        r1 += 1;
                    }
                }
                q2 += 1;
            }
            q1 += 1;
        }

        dp = next;
        i += 1;
    }

    let mut ans = neg;
    let mut a = 0usize;
    while a < cols {
        let mut b = 0usize;
        while b < cols {
            let v = dp[a * cols + b];
            if v > ans {
                ans = v;
            }
            b += 1;
        }
        a += 1;
    }

    ans
}
