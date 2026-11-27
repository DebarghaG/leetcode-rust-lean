fn move_id(c: u8) -> usize {
    if c == b'F' {
        0
    } else if c == b'W' {
        1
    } else {
        2
    }
}

fn gain(bob: usize, alice: usize) -> i64 {
    if bob == alice {
        0
    } else if (bob == 0 && alice == 2)
        || (bob == 1 && alice == 0)
        || (bob == 2 && alice == 1)
    {
        1
    } else {
        -1
    }
}

pub fn count_winning_sequences(s: &[u8]) -> i64 {
    let n = s.len();
    let m = 2 * n + 1;
    let modulo: i64 = 1000000007;

    let mut dp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < 3 * m {
        dp.push(0);
        z += 1;
    }

    let a0 = move_id(s[0]);
    let mut b: usize = 0;
    while b < 3 {
        let g = gain(b, a0);
        let idx = if g == 1 {
            n + 1
        } else if g == -1 {
            n - 1
        } else {
            n
        };

        let pos = b * m + idx;
        dp[pos] = (dp[pos] + 1) % modulo;
        b += 1;
    }

    let mut i: usize = 1;
    while i < n {
        let a = move_id(s[i]);

        let mut ndp: Vec<i64> = Vec::new();
        let mut z2: usize = 0;
        while z2 < 3 * m {
            ndp.push(0);
            z2 += 1;
        }

        let mut last: usize = 0;
        while last < 3 {
            let base = last * m;

            let mut idx: usize = 0;
            while idx < m {
                let val = dp[base + idx];

                if val != 0 {
                    let mut cur: usize = 0;
                    while cur < 3 {
                        if cur != last {
                            let g = gain(cur, a);
                            let mut nidx = idx;

                            if g == 1 {
                                nidx = idx + 1;
                            } else if g == -1 {
                                nidx = idx - 1;
                            }

                            let npos = cur * m + nidx;
                            ndp[npos] = (ndp[npos] + val) % modulo;
                        }
                        cur += 1;
                    }
                }

                idx += 1;
            }

            last += 1;
        }

        dp = ndp;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut last: usize = 0;
    while last < 3 {
        let base = last * m;

        let mut idx = n + 1;
        while idx < m {
            ans = (ans + dp[base + idx]) % modulo;
            idx += 1;
        }

        last += 1;
    }

    ans
}
