const MOD: i64 = 1_000_000_007;

fn make_zeros(size: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < size {
        v.push(0);
        i += 1;
    }
    v
}

pub fn num_of_arrays(n: i64, m: i64, k: i64) -> i64 {
    if n <= 0 || m <= 0 || k <= 0 {
        return 0;
    }
    if k > n || k > m {
        return 0;
    }

    let nn: usize = n as usize;
    let mm: usize = m as usize;
    let kk: usize = k as usize;

    let rmax: usize = if nn < mm { nn } else { mm };
    if kk > rmax {
        return 0;
    }

    // s2[r] = Stirling number of the second kind S(nn, r).
    let mut s2: Vec<i64> = make_zeros(rmax + 1);
    s2[0] = 1;

    let mut i: usize = 1;
    while i <= nn {
        let upper: usize = if i < rmax { i } else { rmax };
        let mut j: usize = upper;
        while j > 0 {
            let term: i64 = (j as i64) * s2[j] % MOD;
            s2[j] = (s2[j - 1] + term) % MOD;
            j -= 1;
        }
        s2[0] = 0;
        i += 1;
    }

    // binom[r] = C(mm, r).
    let mut binom: Vec<i64> = make_zeros(rmax + 1);
    binom[0] = 1;

    let mut a: usize = 1;
    while a <= mm {
        let upper: usize = if a < rmax { a } else { rmax };
        let mut j: usize = upper;
        while j > 0 {
            binom[j] = (binom[j] + binom[j - 1]) % MOD;
            j -= 1;
        }
        a += 1;
    }

    // c_at[r] = unsigned Stirling number of the first kind c(r, kk).
    let mut c_at: Vec<i64> = make_zeros(rmax + 1);
    let mut prev: Vec<i64> = make_zeros(kk + 1);
    prev[0] = 1;

    let mut r: usize = 1;
    while r <= rmax {
        let upper: usize = if r < kk { r } else { kk };
        let factor: i64 = (r as i64) - 1;

        let mut j: usize = upper;
        while j > 0 {
            let term: i64 = factor * prev[j] % MOD;
            prev[j] = (prev[j - 1] + term) % MOD;
            j -= 1;
        }
        prev[0] = 0;

        if kk <= r {
            c_at[r] = prev[kk];
        }

        r += 1;
    }

    let mut answer: i64 = 0;
    let mut rr: usize = kk;
    while rr <= rmax {
        let term1: i64 = s2[rr] * binom[rr] % MOD;
        let term2: i64 = term1 * c_at[rr] % MOD;
        answer = (answer + term2) % MOD;
        rr += 1;
    }

    answer
}
