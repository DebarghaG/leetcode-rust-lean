pub fn count_palindromes(s: &[u8]) -> i64 {
    const MOD: i64 = 1000000007;

    let n = s.len();
    if n < 5 {
        return 0;
    }

    // suf_pairs[k] stores counts of ordered pairs (i, j) with
    // k < i < j, flattened as first_digit * 10 + second_digit.
    let total = n * 100;
    let mut suf_pairs: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z < total {
        suf_pairs.push(0i64);
        z += 1;
    }

    let mut cnt: Vec<i64> = Vec::new();
    z = 0;
    while z < 10 {
        cnt.push(0i64);
        z += 1;
    }

    let mut cur_pairs: Vec<i64> = Vec::new();
    z = 0;
    while z < 100 {
        cur_pairs.push(0i64);
        z += 1;
    }

    let mut kk = n;
    while kk > 0 {
        kk -= 1;

        let base = kk * 100;
        let mut idx = 0usize;
        while idx < 100 {
            suf_pairs[base + idx] = cur_pairs[idx];
            idx += 1;
        }

        let d = (s[kk] as i64) - 48;
        let du = d as usize;

        let mut e = 0usize;
        while e < 10 {
            let add = cnt[e];
            if add != 0 {
                let p = du * 10 + e;
                cur_pairs[p] = (cur_pairs[p] + add) % MOD;
            }
            e += 1;
        }

        cnt[du] = (cnt[du] + 1) % MOD;
    }

    let mut left_cnt: Vec<i64> = Vec::new();
    z = 0;
    while z < 10 {
        left_cnt.push(0i64);
        z += 1;
    }

    let mut left_pairs: Vec<i64> = Vec::new();
    z = 0;
    while z < 100 {
        left_pairs.push(0i64);
        z += 1;
    }

    let mut ans: i64 = 0;
    let mut k = 0usize;

    while k < n {
        let base = k * 100;

        let mut a = 0usize;
        while a < 10 {
            let mut b = 0usize;
            while b < 10 {
                let lp = left_pairs[a * 10 + b];
                let rp = suf_pairs[base + b * 10 + a];

                if lp != 0 && rp != 0 {
                    ans = (ans + (lp * rp) % MOD) % MOD;
                }

                b += 1;
            }
            a += 1;
        }

        let d = (s[k] as i64) - 48;
        let du = d as usize;

        let mut e = 0usize;
        while e < 10 {
            let add = left_cnt[e];
            if add != 0 {
                let p = e * 10 + du;
                left_pairs[p] = (left_pairs[p] + add) % MOD;
            }
            e += 1;
        }

        left_cnt[du] = (left_cnt[du] + 1) % MOD;

        k += 1;
    }

    ans
}
