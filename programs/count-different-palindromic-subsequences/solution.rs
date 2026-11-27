const MOD: i64 = 1000000007;

fn norm(x: i64) -> i64 {
    let mut y = x % MOD;
    if y < 0 {
        y += MOD;
    }
    y
}

pub fn count_palindromic_subsequences(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut next_pos: Vec<Vec<i64>> = Vec::new();
    let mut init_i = 0;
    while init_i < n {
        let mut row: Vec<i64> = Vec::new();
        let mut k = 0;
        while k < 4 {
            row.push(0);
            k += 1;
        }
        next_pos.push(row);
        init_i += 1;
    }

    let mut prev_pos: Vec<Vec<i64>> = Vec::new();
    let mut init_j = 0;
    while init_j < n {
        let mut row: Vec<i64> = Vec::new();
        let mut k = 0;
        while k < 4 {
            row.push(0);
            k += 1;
        }
        prev_pos.push(row);
        init_j += 1;
    }

    let mut ii = n;
    while ii > 0 {
        ii -= 1;
        let ci = (s[ii] - b'a') as usize;
        let mut k = 0;
        while k < 4 {
            if k == ci {
                next_pos[ii][k] = ii as i64;
            } else if ii + 1 < n {
                next_pos[ii][k] = next_pos[ii + 1][k];
            } else {
                next_pos[ii][k] = n as i64;
            }
            k += 1;
        }
    }

    let mut jj = 0;
    while jj < n {
        let ci = (s[jj] - b'a') as usize;
        let mut k = 0;
        while k < 4 {
            if k == ci {
                prev_pos[jj][k] = jj as i64;
            } else if jj > 0 {
                prev_pos[jj][k] = prev_pos[jj - 1][k];
            } else {
                prev_pos[jj][k] = -1;
            }
            k += 1;
        }
        jj += 1;
    }

    let mut dp: Vec<Vec<i64>> = Vec::new();
    let mut r = 0;
    while r < n {
        let mut row: Vec<i64> = Vec::new();
        let mut c = 0;
        while c < n {
            row.push(0);
            c += 1;
        }
        dp.push(row);
        r += 1;
    }

    let mut len = 1;
    while len <= n {
        let mut i = 0;
        while i + len <= n {
            let j = i + len - 1;

            if len == 1 {
                dp[i][j] = 1;
            } else {
                if s[i] != s[j] {
                    let mut val = dp[i + 1][j] + dp[i][j - 1];
                    if i + 1 <= j - 1 {
                        val -= dp[i + 1][j - 1];
                    }
                    dp[i][j] = norm(val);
                } else {
                    let mut inner = 0;
                    if i + 1 <= j - 1 {
                        inner = dp[i + 1][j - 1];
                    }

                    let ci = (s[i] - b'a') as usize;

                    let mut l = n as i64;
                    if i + 1 < n {
                        l = next_pos[i + 1][ci];
                    }

                    let mut rr = -1;
                    if j > 0 {
                        rr = prev_pos[j - 1][ci];
                    }

                    let ii64 = i as i64;
                    let jj64 = j as i64;

                    if l < jj64 && rr > ii64 {
                        if l == rr {
                            dp[i][j] = norm(2 * inner + 1);
                        } else {
                            let mut sub = 0;
                            if l + 1 <= rr - 1 {
                                let li = (l + 1) as usize;
                                let ri = (rr - 1) as usize;
                                sub = dp[li][ri];
                            }
                            dp[i][j] = norm(2 * inner - sub);
                        }
                    } else {
                        dp[i][j] = norm(2 * inner + 2);
                    }
                }
            }

            i += 1;
        }
        len += 1;
    }

    dp[0][n - 1]
}
