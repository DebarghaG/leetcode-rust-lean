fn is_prime(n: i64) -> bool {
    if n < 2 {
        return false;
    }

    let mut d: i64 = 2;
    while d * d <= n {
        if n % d == 0 {
            return false;
        }
        d += 1;
    }

    true
}

pub fn non_special_count(l: i64, r: i64) -> i64 {
    let total = r - l + 1;
    let mut special: i64 = 0;
    let mut p: i64 = 2;

    while p * p <= r {
        if p * p >= l && is_prime(p) {
            special += 1;
        }
        p += 1;
    }

    total - special
}
