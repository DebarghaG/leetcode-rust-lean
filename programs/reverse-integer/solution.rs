pub fn reverse(x: i64) -> i64 {
    let limit: i64 = 2147483647;
    let min_limit: i64 = -2147483648;

    let negative = x < 0;
    let mut n = x;
    if negative {
        n = -n;
    }

    let mut rev: i64 = 0;
    while n != 0 {
        let digit = n % 10;
        n = n / 10;
        rev = rev * 10 + digit;
    }

    if negative {
        rev = -rev;
    }

    if rev < min_limit || rev > limit {
        0
    } else {
        rev
    }
}
