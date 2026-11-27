pub fn digits_count(d: i64, low: i64, high: i64) -> i64 {
    count_upto(d, high) - count_upto(d, low - 1)
}

fn count_upto(d: i64, n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut factor: i64 = 1;

    while factor <= n {
        let base: i64 = factor * 10;
        let higher: i64 = n / base;
        let cur: i64 = (n / factor) % 10;
        let lower: i64 = n % factor;

        if d == 0 {
            if higher > 0 {
                if cur == 0 {
                    total = total + (higher - 1) * factor + lower + 1;
                } else {
                    total = total + higher * factor;
                }
            }
        } else {
            if cur > d {
                total = total + (higher + 1) * factor;
            } else if cur == d {
                total = total + higher * factor + lower + 1;
            } else {
                total = total + higher * factor;
            }
        }

        factor = factor * 10;
    }

    total
}
