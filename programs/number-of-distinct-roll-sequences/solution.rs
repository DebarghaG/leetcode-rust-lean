const MOD: i64 = 1000000007;

fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

pub fn distinct_sequences(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }
    if n == 1 {
        return 6;
    }

    // dp[a * 6 + b] = number of valid sequences ending with the two rolls (a+1, b+1)
    let mut dp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 36 {
        dp.push(0);
        i += 1;
    }

    let mut a: usize = 0;
    while a < 6 {
        let mut b: usize = 0;
        while b < 6 {
            if a != b && gcd((a as i64) + 1, (b as i64) + 1) == 1 {
                dp[a * 6 + b] = 1;
            }
            b += 1;
        }
        a += 1;
    }

    if n == 2 {
        let mut total: i64 = 0;
        let mut j: usize = 0;
        while j < 36 {
            total += dp[j];
            if total >= MOD {
                total -= MOD;
            }
            j += 1;
        }
        return total;
    }

    let mut step: i64 = 3;
    while step <= n {
        let mut next: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 36 {
            next.push(0);
            k += 1;
        }

        let mut x: usize = 0;
        while x < 6 {
            let mut y: usize = 0;
            while y < 6 {
                let val = dp[x * 6 + y];
                if val != 0 {
                    let mut d: usize = 0;
                    while d < 6 {
                        if d != x && d != y && gcd((y as i64) + 1, (d as i64) + 1) == 1 {
                            let idx: usize = y * 6 + d;
                            let s = next[idx] + val;
                            if s >= MOD {
                                next[idx] = s - MOD;
                            } else {
                                next[idx] = s;
                            }
                        }
                        d += 1;
                    }
                }
                y += 1;
            }
            x += 1;
        }

        dp = next;
        step += 1;
    }

    let mut total: i64 = 0;
    let mut j: usize = 0;
    while j < 36 {
        total += dp[j];
        if total >= MOD {
            total -= MOD;
        }
        j += 1;
    }

    total
}
