const MOD: i64 = 1_000_000_007;

fn mod_pow(mut base: i64, mut exp: i64) -> i64 {
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

pub fn max_nice_divisors(primeFactors: i64) -> i64 {
    if primeFactors <= 3 {
        return primeFactors;
    }

    let q: i64 = primeFactors / 3;
    let r: i64 = primeFactors % 3;

    if r == 0 {
        return mod_pow(3, q);
    }

    if r == 1 {
        return (4 * mod_pow(3, q - 1)) % MOD;
    }

    (2 * mod_pow(3, q)) % MOD
}
