const MOD: i64 = 1000000007;

fn gcd_usize(a0: usize, b0: usize) -> usize {
    let mut a = a0;
    let mut b = b0;
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn mobius(x: usize) -> i64 {
    let mut n = x;
    let mut p = 2usize;
    let mut count = 0i64;

    while p * p <= n {
        if n % p == 0 {
            let mut exp = 0;
            while n % p == 0 {
                n /= p;
                exp += 1;
            }
            if exp >= 2 {
                return 0;
            }
            count += 1;
        }
        p += 1;
    }

    if n > 1 {
        count += 1;
    }

    if count % 2 == 0 {
        1
    } else {
        -1
    }
}

pub fn subsequence_pair_count(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut maxv: i64 = 0;
    let mut i = 0;
    while i < n {
        if nums[i] > maxv {
            maxv = nums[i];
        }
        i += 1;
    }

    let m = maxv as usize;
    if m == 0 {
        return 0;
    }

    // cnt[d] = number of elements divisible by d
    let mut cnt: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z <= m {
        cnt.push(0);
        z += 1;
    }

    let mut d = 1usize;
    while d <= m {
        let dd = d as i64;
        let mut c = 0i64;
        let mut j = 0usize;
        while j < n {
            if nums[j] % dd == 0 {
                c += 1;
            }
            j += 1;
        }
        cnt[d] = c;
        d += 1;
    }

    // Powers of 2 and 3 up to n.
    let mut pow2: Vec<i64> = Vec::new();
    let mut pow3: Vec<i64> = Vec::new();
    pow2.push(1);
    pow3.push(1);

    let mut k = 1usize;
    while k <= n {
        let v2 = (pow2[k - 1] * 2) % MOD;
        let v3 = (pow3[k - 1] * 3) % MOD;
        pow2.push(v2);
        pow3.push(v3);
        k += 1;
    }

    // Mobius values up to m.
    let mut mu: Vec<i64> = Vec::new();
    mu.push(0);
    let mut q = 1usize;
    while q <= m {
        mu.push(mobius(q));
        q += 1;
    }

    let mut ans: i64 = 0;

    let mut d = 1usize;
    while d <= m {
        let cd = cnt[d];
        let mut e = 1usize;
        while e <= m {
            let ce = cnt[e];

            let h = gcd_usize(d, e);
            let l = (d / h) * e;

            let mut both = 0i64;
            if l <= m {
                both = cnt[l];
            }

            let d_only = cd - both;
            let e_only = ce - both;
            let exp = (d_only + e_only) as usize;

            // Q(d,e): disjoint non-empty pairs A subset T_d, B subset T_e.
            let mut qval = (pow3[both as usize] * pow2[exp]) % MOD;
            qval = qval - pow2[ce as usize] - pow2[cd as usize] + 1;
            qval %= MOD;
            if qval < 0 {
                qval += MOD;
            }

            // S(d,e) = sum_{g | gcd(d,e)} mu(d/g) * mu(e/g).
            let mut s: i64 = 0;
            let mut g = 1usize;
            while g <= h {
                if h % g == 0 {
                    s += mu[d / g] * mu[e / g];
                }
                g += 1;
            }

            if s != 0 {
                if qval != 0 {
                    let mut term = (qval * s) % MOD;
                    if term < 0 {
                        term += MOD;
                    }
                    ans += term;
                    if ans >= MOD {
                        ans -= MOD;
                    }
                }
            }

            e += 1;
        }
        d += 1;
    }

    ans
}
