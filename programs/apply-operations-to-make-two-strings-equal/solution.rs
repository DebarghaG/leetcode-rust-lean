pub fn min_operations(s1: &[u8], s2: &[u8], x: i64) -> i64 {
    let n = s1.len();
    let mut pos: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        if s1[i] != s2[i] {
            pos.push(i as i64);
        }
        i += 1;
    }

    let m = pos.len();
    if m % 2 == 1 {
        return -1;
    }
    if m == 0 {
        return 0;
    }

    // dp state:
    //   b = 0/1: whether there is an unmatched mismatch kept for adjacent flips
    //   a = 0/1: parity of mismatches assigned to the arbitrary-pair operation
    // state index = b * 2 + a
    let inf: i64 = 1_000_000_000;
    let mut dp: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 4 {
        dp.push(inf);
        k += 1;
    }
    dp[0] = 0;

    let mut idx: usize = 0;
    while idx < m {
        let p = pos[idx];
        let mut ndp: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < 4 {
            ndp.push(inf);
            q += 1;
        }

        let mut b: usize = 0;
        while b < 2 {
            let mut a: usize = 0;
            while a < 2 {
                let val = dp[b * 2 + a];
                if val < inf / 2 {
                    // Use this mismatch for adjacent flips.
                    if b == 0 {
                        // Open an adjacent pair: later closing adds its position.
                        let nv = val - p;
                        let state = 2 + a;
                        if nv < ndp[state] {
                            ndp[state] = nv;
                        }
                    } else {
                        // Close the currently open adjacent pair.
                        let nv = val + p;
                        let state = a;
                        if nv < ndp[state] {
                            ndp[state] = nv;
                        }
                    }

                    // Use this mismatch for an arbitrary-pair operation.
                    if a == 0 {
                        // Open an arbitrary pair.
                        let nv = val;
                        let state = b * 2 + 1;
                        if nv < ndp[state] {
                            ndp[state] = nv;
                        }
                    } else {
                        // Close the arbitrary pair, paying x.
                        let nv = val + x;
                        let state = b * 2;
                        if nv < ndp[state] {
                            ndp[state] = nv;
                        }
                    }
                }
                a += 1;
            }
            b += 1;
        }

        dp = ndp;
        idx += 1;
    }

    dp[0]
}
