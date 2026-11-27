const MOD: i64 = 1_000_000_007;

fn mod_pow(mut base: i64, mut exp: i64) -> i64 {
    base %= MOD;
    let mut result: i64 = 1;
    while exp > 0 {
        if exp % 2 == 1 {
            result = result * base % MOD;
        }
        base = base * base % MOD;
        exp /= 2;
    }
    result
}

fn comb(n: usize, k: usize, fact: &[i64], invfact: &[i64]) -> i64 {
    if k > n {
        return 0;
    }
    let mut result = fact[n] * invfact[k] % MOD;
    result = result * invfact[n - k] % MOD;
    result
}

// Number of ways to write n as an ordered sum of exactly k positive integers,
// each at most limit.
fn ways(
    n: usize,
    k: usize,
    limit: usize,
    fact: &[i64],
    invfact: &[i64],
) -> i64 {
    if k == 0 {
        if n == 0 {
            return 1;
        }
        return 0;
    }
    if k > n {
        return 0;
    }
    if n > k * limit {
        return 0;
    }

    let jmax = (n - k) / limit;
    let mut result: i64 = 0;
    let mut j: usize = 0;

    while j <= jmax {
        let top = n - j * limit - 1;
        let term = comb(k, j, fact, invfact) * comb(top, k - 1, fact, invfact) % MOD;

        if j % 2 == 0 {
            result += term;
            if result >= MOD {
                result -= MOD;
            }
        } else {
            result -= term;
            if result < 0 {
                result += MOD;
            }
        }

        j += 1;
    }

    result
}

pub fn number_of_stable_arrays(zero: i64, one: i64, limit: i64) -> i64 {
    let z = zero as usize;
    let o = one as usize;
    let l = limit as usize;

    if z == 0 && o == 0 {
        return 1;
    }

    let max_n = if z > o { z } else { o };

    let mut fact: Vec<i64> = Vec::new();
    fact.push(1);

    let mut i: usize = 1;
    while i <= max_n {
        let prev = fact[i - 1];
        fact.push(prev * (i as i64) % MOD);
        i += 1;
    }

    let mut invfact: Vec<i64> = Vec::new();
    i = 0;
    while i <= max_n {
        invfact.push(0);
        i += 1;
    }

    invfact[max_n] = mod_pow(fact[max_n], MOD - 2);

    i = max_n;
    while i > 0 {
        invfact[i - 1] = invfact[i] * (i as i64) % MOD;
        i -= 1;
    }

    let max_a = if z > o { z } else { o };

    let mut prev_z: i64 = if z == 0 { 1 } else { 0 };
    let mut prev_o: i64 = if o == 0 { 1 } else { 0 };

    let mut ans: i64 = 0;
    let mut a: usize = 1;

    while a <= max_a {
        let fz = ways(z, a, l, &fact, &invfact);
        let fo = ways(o, a, l, &fact, &invfact);

        let equal_runs = fz * fo % MOD;
        let equal_runs_twice = equal_runs * 2 % MOD;

        ans += equal_runs_twice;
        if ans >= MOD {
            ans -= MOD;
        }

        let more_zero_runs = fz * prev_o % MOD;
        ans += more_zero_runs;
        if ans >= MOD {
            ans -= MOD;
        }

        let more_one_runs = fo * prev_z % MOD;
        ans += more_one_runs;
        if ans >= MOD {
            ans -= MOD;
        }

        prev_z = fz;
        prev_o = fo;
        a += 1;
    }

    ans
}
