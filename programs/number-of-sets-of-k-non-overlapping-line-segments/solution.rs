const MOD: i64 = 1_000_000_007;

fn pow_mod(mut base: i64, mut exp: i64) -> i64 {
    let mut result: i64 = 1;
    while exp > 0 {
        if exp % 2 == 1 {
            result = (result * base) % MOD;
        }
        base = (base * base) % MOD;
        exp = exp / 2;
    }
    result
}

pub fn number_of_sets(n: i64, k: i64) -> i64 {
    // The answer is C(n + k - 1, 2k).
    let top: i64 = n + k - 1;
    let bottom: i64 = 2 * k;

    if bottom > top {
        return 0;
    }

    let mut numerator: i64 = 1;
    let mut denominator: i64 = 1;
    let mut i: i64 = 0;

    while i < bottom {
        numerator = (numerator * (top - i)) % MOD;
        denominator = (denominator * (i + 1)) % MOD;
        i += 1;
    }

    let inv_denominator: i64 = pow_mod(denominator, MOD - 2);
    (numerator * inv_denominator) % MOD
}
