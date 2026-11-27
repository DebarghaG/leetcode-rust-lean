const MOD: i64 = 1_000_000_007;

fn mod_pow(mut base: i64, mut exp: i64) -> i64 {
    let mut result: i64 = 1;
    base = base % MOD;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % MOD;
        }
        base = (base * base) % MOD;
        exp = exp / 2;
    }
    result
}

fn binom(n: i64, r: i64) -> i64 {
    if r < 0 {
        return 0;
    }
    if r > n {
        return 0;
    }

    let mut rr = r;
    if n - r < rr {
        rr = n - r;
    }

    let mut numerator: i64 = 1;
    let mut denominator: i64 = 1;
    let mut i: i64 = 1;

    while i <= rr {
        numerator = (numerator * ((n - rr + i) % MOD)) % MOD;
        denominator = (denominator * (i % MOD)) % MOD;
        i += 1;
    }

    let inv = mod_pow(denominator, MOD - 2);
    (numerator * inv) % MOD
}

fn pair_difference_sum(len: i64) -> i64 {
    if len <= 1 {
        return 0;
    }

    let value = len * (len - 1) * (len + 1) / 6;
    value % MOD
}

pub fn distance_sum(m: i64, n: i64, k: i64) -> i64 {
    if k < 2 {
        return 0;
    }

    let total_cells = m * n;
    if total_cells < k {
        return 0;
    }

    let ways = binom(total_cells - 2, k - 2);

    let row_sum = pair_difference_sum(m);
    let col_sum = pair_difference_sum(n);

    let n_mod = n % MOD;
    let m_mod = m % MOD;

    let row_part = (((n_mod * n_mod) % MOD) * row_sum) % MOD;
    let col_part = (((m_mod * m_mod) % MOD) * col_sum) % MOD;

    let all_pair_distances = (row_part + col_part) % MOD;

    (ways * all_pair_distances) % MOD
}
