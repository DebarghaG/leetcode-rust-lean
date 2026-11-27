fn add_digits(mut x: i64, seen: i64) -> i64 {
    let mut bits = seen;
    while x > 0 {
        let d = x % 10;
        if d == 0 {
            return -1;
        }

        let mut bit: i64 = 1;
        let mut k: i64 = 0;
        while k < d {
            bit = bit * 2;
            k = k + 1;
        }

        if bits & bit != 0 {
            return -1;
        }

        bits = bits | bit;
        x = x / 10;
    }
    bits
}

pub fn is_fascinating(n: i64) -> bool {
    let mut seen: i64 = 0;

    seen = add_digits(n, seen);
    if seen == -1 {
        return false;
    }

    seen = add_digits(2 * n, seen);
    if seen == -1 {
        return false;
    }

    seen = add_digits(3 * n, seen);
    if seen == -1 {
        return false;
    }

    seen == 1022
}
