fn make_zeros(size: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        v.push(0);
        i += 1;
    }
    v
}

pub fn die_simulator(n: i64, rollMax: &[i64]) -> i64 {
    let modulo: i64 = 1000000007;
    let faces: usize = rollMax.len();
    let stride: usize = 16;
    let size: usize = faces * stride;

    let mut dp: Vec<i64> = make_zeros(size);

    let mut f: usize = 0;
    while f < faces {
        dp[f * stride + 1] = 1;
        f += 1;
    }

    let mut step: i64 = 2;
    while step <= n {
        let mut ndp: Vec<i64> = make_zeros(size);

        let mut f2: usize = 0;
        while f2 < faces {
            let limit: i64 = rollMax[f2];

            let mut k: usize = 1;
            let mut ki: i64 = 1;
            while k < stride {
                let val: i64 = dp[f2 * stride + k];

                if val != 0 {
                    if ki < limit {
                        let same_idx: usize = f2 * stride + k + 1;
                        let mut nv: i64 = ndp[same_idx] + val;
                        if nv >= modulo {
                            nv -= modulo;
                        }
                        ndp[same_idx] = nv;
                    }

                    let mut g: usize = 0;
                    while g < faces {
                        if g != f2 {
                            let diff_idx: usize = g * stride + 1;
                            let mut nv2: i64 = ndp[diff_idx] + val;
                            if nv2 >= modulo {
                                nv2 -= modulo;
                            }
                            ndp[diff_idx] = nv2;
                        }
                        g += 1;
                    }
                }

                k += 1;
                ki += 1;
            }

            f2 += 1;
        }

        dp = ndp;
        step += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;
    while i < size {
        ans += dp[i];
        if ans >= modulo {
            ans -= modulo;
        }
        i += 1;
    }

    ans
}
