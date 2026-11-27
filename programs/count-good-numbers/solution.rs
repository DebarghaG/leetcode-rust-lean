pub fn count_good_numbers(n: i64) -> i64 {
    const MOD: i64 = 1_000_000_007;

    fn pow_mod(mut base: i64, mut exp: i64, modulus: i64) -> i64 {
        let mut result: i64 = 1;
        base %= modulus;

        while exp > 0 {
            if exp % 2 == 1 {
                result = (result * base) % modulus;
            }
            base = (base * base) % modulus;
            exp /= 2;
        }

        result
    }

    let even_positions = (n + 1) / 2;
    let odd_positions = n / 2;

    let even_ways = pow_mod(5, even_positions, MOD);
    let odd_ways = pow_mod(4, odd_positions, MOD);

    (even_ways * odd_ways) % MOD
}
