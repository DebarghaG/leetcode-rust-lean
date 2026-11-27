fn sum_prime_factors(mut x: i64) -> i64 {
    let mut sum = 0;
    let mut d = 2;

    while d * d <= x {
        while x % d == 0 {
            sum += d;
            x = x / d;
        }
        d += 1;
    }

    if x > 1 {
        sum += x;
    }

    sum
}

pub fn smallest_value(n: i64) -> i64 {
    let mut cur = n;
    let mut next = sum_prime_factors(cur);

    while next != cur {
        cur = next;
        next = sum_prime_factors(cur);
    }

    cur
}
