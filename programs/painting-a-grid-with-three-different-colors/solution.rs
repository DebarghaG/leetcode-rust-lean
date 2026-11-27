const MOD: i64 = 1_000_000_007;

pub fn color_the_grid(m: i64, n: i64) -> i64 {
    let m_us = m as usize;

    // There are 3^m possible color sequences for one column.
    let mut total_codes: i64 = 1;
    let mut i: i64 = 0;
    while i < m {
        total_codes *= 3;
        i += 1;
    }

    // Generate all vertically valid column colorings.
    let mut states: Vec<Vec<i64>> = Vec::new();
    let mut code: i64 = 0;
    while code < total_codes {
        let mut col: Vec<i64> = Vec::new();
        let mut x = code;
        let mut r = 0usize;
        while r < m_us {
            col.push(x % 3);
            x /= 3;
            r += 1;
        }

        let mut ok = true;
        let mut r2 = 1usize;
        while r2 < m_us {
            if col[r2] == col[r2 - 1] {
                ok = false;
            }
            r2 += 1;
        }

        if ok {
            states.push(col);
        }
        code += 1;
    }

    let s = states.len();

    // dp[p] = number of ways to paint up to the previous column,
    // ending with vertically valid column state p.
    let mut dp: Vec<i64> = Vec::new();
    let mut idx = 0usize;
    while idx < s {
        dp.push(1);
        idx += 1;
    }

    let mut c: i64 = 1;
    while c < n {
        let mut ndp: Vec<i64> = Vec::new();

        let mut t = 0usize;
        while t < s {
            let mut sum: i64 = 0;

            let mut p = 0usize;
            while p < s {
                let mut compatible = true;
                let mut row = 0usize;

                while row < m_us {
                    if states[p][row] == states[t][row] {
                        compatible = false;
                    }
                    row += 1;
                }

                if compatible {
                    sum += dp[p];
                    if sum >= MOD {
                        sum -= MOD;
                    }
                }

                p += 1;
            }

            ndp.push(sum);
            t += 1;
        }

        dp = ndp;
        c += 1;
    }

    let mut ans: i64 = 0;
    let mut j = 0usize;
    while j < s {
        ans += dp[j];
        if ans >= MOD {
            ans -= MOD;
        }
        j += 1;
    }

    ans
}
