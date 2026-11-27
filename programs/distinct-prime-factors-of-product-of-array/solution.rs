pub fn distinct_prime_factors(nums: &[i64]) -> i64 {
    let mut primes: Vec<i64> = Vec::new();
    let mut count: i64 = 0;

    let mut i: usize = 0;
    while i < nums.len() {
        let mut x: i64 = nums[i];
        let mut d: i64 = 2;

        while d * d <= x {
            if x % d == 0 {
                let mut found: bool = false;
                let mut j: usize = 0;
                while j < primes.len() {
                    if primes[j] == d {
                        found = true;
                    }
                    j += 1;
                }

                if !found {
                    primes.push(d);
                    count += 1;
                }

                while x % d == 0 {
                    x = x / d;
                }
            }

            d += 1;
        }

        if x > 1 {
            let mut found: bool = false;
            let mut j: usize = 0;
            while j < primes.len() {
                if primes[j] == x {
                    found = true;
                }
                j += 1;
            }

            if !found {
                primes.push(x);
                count += 1;
            }
        }

        i += 1;
    }

    count
}
