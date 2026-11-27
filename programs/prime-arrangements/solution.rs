pub fn num_prime_arrangements(n: i64) -> i64 {
    let mut prime_count: i64 = 0;
    let mut i: i64 = 2;

    while i <= n {
        let mut is_prime: bool = true;
        let mut d: i64 = 2;

        while d * d <= i {
            if i % d == 0 {
                is_prime = false;
                break;
            }
            d += 1;
        }

        if is_prime {
            prime_count += 1;
        }

        i += 1;
    }

    let modulus: i64 = 1000000007;
    let mut ans: i64 = 1;

    let mut k: i64 = 1;
    while k <= prime_count {
        ans = (ans * k) % modulus;
        k += 1;
    }

    let non_primes: i64 = n - prime_count;
    let mut j: i64 = 1;
    while j <= non_primes {
        ans = (ans * j) % modulus;
        j += 1;
    }

    ans
}
