pub fn is_armstrong(n: i64) -> bool {
    let mut digits: i64 = 0;
    let mut temp: i64 = n;

    while temp > 0 {
        digits += 1;
        temp /= 10;
    }

    let mut remaining: i64 = n;
    let mut total: i64 = 0;

    while remaining > 0 {
        let digit: i64 = remaining % 10;
        let mut power: i64 = 1;
        let mut i: i64 = 0;

        while i < digits {
            power *= digit;
            i += 1;
        }

        total += power;
        remaining /= 10;
    }

    total == n
}
