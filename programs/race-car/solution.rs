fn dp_solve(s_val: i64, d: i64, smax: i64) -> i64 {
    let cmax: i64 = 4;
    let emax: usize = 20;
    let inf: i64 = 1_000_000_000;

    let vn: usize = (2 * cmax + 1) as usize;
    let sn: usize = (2 * smax + 1) as usize;
    let total: usize = vn * sn;

    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dp.push(inf);
        i = i + 1;
    }

    // state (v = 0, s = 0)
    dp[(cmax as usize) * sn + (smax as usize)] = 0;

    let mut sbits: i64 = s_val;
    let mut e: usize = 0;

    while e <= emax {
        let bit: i64 = sbits % 2;

        let mut ndp: Vec<i64> = Vec::new();
        i = 0;
        while i < total {
            ndp.push(inf);
            i = i + 1;
        }

        let mut vi: usize = 0;
        while vi < vn {
            let v: i64 = vi as i64 - cmax;

            let mut si: usize = 0;
            while si < sn {
                let old_cost: i64 = dp[vi * sn + si];

                if old_cost < inf {
                    let s_actual: i64 = si as i64 - smax;

                    let mut c: i64 = -cmax;
                    while c <= cmax {
                        let sumvc: i64 = v + c;

                        if (sumvc - bit) % 2 == 0 {
                            let v2: i64 = (sumvc - bit) / 2;

                            if v2 >= -cmax && v2 <= cmax {
                                let s2: i64 = s_actual + c;

                                if s2 >= -smax && s2 <= smax {
                                    let abs_c: i64 = if c < 0 { -c } else { c };
                                    let add: i64 = (e as i64 + 1) * abs_c;
                                    let new_cost: i64 = old_cost + add;

                                    let idx2: usize =
                                        ((v2 + cmax) as usize) * sn
                                        + ((s2 + smax) as usize);

                                    if new_cost < ndp[idx2] {
                                        ndp[idx2] = new_cost;
                                    }
                                }
                            }
                        }

                        c = c + 1;
                    }
                }

                si = si + 1;
            }

            vi = vi + 1;
        }

        dp = ndp;
        sbits = sbits / 2;
        e = e + 1;
    }

    let final_idx: usize =
        (cmax as usize) * sn + ((d + smax) as usize);

    dp[final_idx]
}

pub fn racecar(target: i64) -> i64 {
    // A loose but valid upper bound, used only to bound the sum of coefficients.
    let mut t: i64 = target;
    let mut ub: i64 = 0;

    while t > 0 {
        let mut n: i64 = 1;
        let mut pow: i64 = 2;

        while pow - 1 < t {
            pow = pow * 2;
            n = n + 1;
        }

        let m: i64 = pow - 1;

        if t == m {
            ub = ub + n;
            t = 0;
        } else {
            ub = ub + n + 1;
            t = m - t;
        }
    }

    let smax: i64 = ub + 2;
    let inf: i64 = 1_000_000_000;
    let mut ans: i64 = inf;

    let c0: i64 = dp_solve(target, 0, smax);
    if c0 < inf {
        let cand: i64 = c0 - 1;
        if cand < ans {
            ans = cand;
        }
    }

    let c1: i64 = dp_solve(target + 1, 1, smax);
    if c1 < inf {
        let cand: i64 = c1 - 1;
        if cand < ans {
            ans = cand;
        }
    }

    ans
}
