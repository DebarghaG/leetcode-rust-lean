const MOD: i64 = 1_000_000_007;

fn digit_index(b: u8) -> usize {
    if b == b'0' {
        0
    } else if b == b'1' {
        1
    } else if b == b'2' {
        2
    } else if b == b'3' {
        3
    } else if b == b'4' {
        4
    } else if b == b'5' {
        5
    } else if b == b'6' {
        6
    } else if b == b'7' {
        7
    } else if b == b'8' {
        8
    } else if b == b'9' {
        9
    } else {
        0
    }
}

fn to_usize_small(v: i64) -> usize {
    let mut u: usize = 0;
    let mut k: i64 = 0;
    while k < v {
        k += 1;
        u += 1;
    }
    u
}

fn mod_pow(mut base: i64, mut exp: i64) -> i64 {
    let mut res: i64 = 1;
    base = base % MOD;
    while exp > 0 {
        if exp % 2 == 1 {
            res = (res * base) % MOD;
        }
        base = (base * base) % MOD;
        exp = exp / 2;
    }
    res
}

pub fn count_balanced_permutations(num: &[u8]) -> i64 {
    let velunexorai = num;
    let n: usize = velunexorai.len();
    if n == 0 {
        return 0;
    }

    let mut cnt: Vec<i64> = Vec::new();
    let mut d: usize = 0;
    while d < 10 {
        cnt.push(0);
        d += 1;
    }

    let mut total_sum: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let b: u8 = velunexorai[i];
        let idx: usize = digit_index(b);

        let mut newcnt: Vec<i64> = Vec::new();
        let mut dd: usize = 0;
        while dd < 10 {
            let old: i64 = cnt[dd];
            if dd == idx {
                newcnt.push(old + 1);
            } else {
                newcnt.push(old);
            }
            dd += 1;
        }
        cnt = newcnt;

        total_sum = total_sum + idx;
        i += 1;
    }

    if total_sum % 2 != 0 {
        return 0;
    }

    let target: usize = total_sum / 2;
    let e: usize = (n + 1) / 2;
    let o: usize = n / 2;

    let mut fact: Vec<i64> = Vec::new();
    fact.push(1);
    let mut fi: usize = 1;
    let mut fval: i64 = 1;
    while fi <= n {
        let prev: i64 = fact[fi - 1];
        let cur: i64 = (prev * fval) % MOD;
        fact.push(cur);
        fi += 1;
        fval += 1;
    }

    let mut invfact: Vec<i64> = Vec::new();
    let mut ii: usize = 0;
    while ii <= n {
        let val: i64 = mod_pow(fact[ii], MOD - 2);
        invfact.push(val);
        ii += 1;
    }

    let width: usize = target + 1;
    let size: usize = (e + 1) * width;

    let mut dp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < size {
        if t == 0 {
            dp.push(1);
        } else {
            dp.push(0);
        }
        t += 1;
    }

    let mut digit: usize = 0;
    while digit < 10 {
        let c_i: i64 = cnt[digit];
        let c_u: usize = to_usize_small(c_i);
        let digit_u: usize = digit;

        let mut ndp: Vec<i64> = Vec::new();

        let mut u: usize = 0;
        while u <= e {
            let mut s: usize = 0;
            while s < width {
                let mut val: i64 = 0;

                let mut x: usize = 0;
                let mut sub: usize = 0;
                while x <= c_u {
                    if x <= u && sub <= s {
                        let prev_u: usize = u - x;
                        let prev_s: usize = s - sub;
                        let idx_dp: usize = prev_u * width + prev_s;
                        let cur: i64 = dp[idx_dp];

                        if cur != 0 {
                            let w: i64 = (invfact[x] * invfact[c_u - x]) % MOD;
                            let add: i64 = (cur * w) % MOD;
                            val = (val + add) % MOD;
                        }
                    }
                    x += 1;
                    sub += digit_u;
                }

                ndp.push(val);
                s += 1;
            }
            u += 1;
        }

        dp = ndp;
        digit += 1;
    }

    let idx_ans: usize = e * width + target;
    let mut ans: i64 = dp[idx_ans];
    ans = (ans * fact[e]) % MOD;
    ans = (ans * fact[o]) % MOD;
    ans
}
