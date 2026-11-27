pub fn maximum_score(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }

    let m = n + 1;
    let neg: i64 = -1000000000000000000;
    let valid_cut: i64 = -500000000000000000;

    // Column-major prefix sums:
    // pref[col * m + t] = sum of grid[0..t-1][col].
    let mut pref: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        let mut s: i64 = 0;
        pref.push(0);
        let mut r: usize = 0;
        while r < n {
            s += grid[r][j];
            pref.push(s);
            r += 1;
        }
        j += 1;
    }

    // dp[a * m + b], where a and b are the last two chosen column heights.
    let total = m * m;
    let mut dp: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < total {
        dp.push(neg);
        idx += 1;
    }

    // Before column 0, the artificial previous height is 0.
    let mut h: usize = 0;
    while h < m {
        dp[h] = 0;
        h += 1;
    }

    let mut col: usize = 0;
    while col + 1 < n {
        let base = col * m;
        let mut newdp: Vec<i64> = Vec::new();

        let mut b: usize = 0;
        while b < m {
            // suff_within[t] = max over a in [t, b] of dp[a * m + b].
            let mut suff_within: Vec<i64> = Vec::new();
            let mut t: usize = 0;
            while t < m {
                suff_within.push(neg);
                t += 1;
            }

            let mut run: i64 = neg;
            let mut aa: usize = b + 1;
            while aa > 0 {
                aa -= 1;
                let val = dp[aa * m + b];
                if val > run {
                    run = val;
                }
                suff_within[aa] = run;
            }

            // suff_with[t] = max over a in [t, m-1] of
            // dp[a * m + b] + pref[base + a] - pref[base + b].
            let mut suff_with: Vec<i64> = Vec::new();
            t = 0;
            while t < m {
                suff_with.push(neg);
                t += 1;
            }

            run = neg;
            let p_b = pref[base + b];
            let mut aa2: usize = m;
            while aa2 > 0 {
                aa2 -= 1;
                let val = dp[aa2 * m + b];
                if val > valid_cut {
                    let cand = val + pref[base + aa2] - p_b;
                    if cand > run {
                        run = cand;
                    }
                }
                suff_with[aa2] = run;
            }

            let mut run_pref: i64 = neg;
            let mut c: usize = 0;
            while c < m {
                let val_c = dp[c * m + b];
                if val_c > run_pref {
                    run_pref = val_c;
                }

                let mut best_c: i64 = neg;

                // Case a <= c.
                if run_pref > valid_cut {
                    let mut extra: i64 = 0;
                    if c > b {
                        extra = pref[base + c] - pref[base + b];
                    }
                    let cand = run_pref + extra;
                    if cand > best_c {
                        best_c = cand;
                    }
                }

                // Case a > c and a <= b.
                if c < b {
                    let cand2 = suff_within[c + 1];
                    if cand2 > best_c {
                        best_c = cand2;
                    }
                }

                // Case a > c and a > b.
                let mut tstart = b + 1;
                if c > b {
                    tstart = c + 1;
                }
                if tstart < m {
                    let cand3 = suff_with[tstart];
                    if cand3 > best_c {
                        best_c = cand3;
                    }
                }

                newdp.push(best_c);
                c += 1;
            }

            b += 1;
        }

        dp = newdp;
        col += 1;
    }

    // Finalize the last column, assuming the artificial next height is 0.
    let base_last = (n - 1) * m;
    let mut ans: i64 = 0;
    let mut a_final: usize = 0;
    while a_final < m {
        let mut b_final: usize = 0;
        while b_final < m {
            let val = dp[a_final * m + b_final];
            if val > valid_cut {
                let mut extra: i64 = 0;
                if a_final > b_final {
                    extra = pref[base_last + a_final] - pref[base_last + b_final];
                }
                let cand = val + extra;
                if cand > ans {
                    ans = cand;
                }
            }
            b_final += 1;
        }
        a_final += 1;
    }

    ans
}
