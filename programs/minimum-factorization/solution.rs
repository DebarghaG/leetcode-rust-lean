pub fn smallest_factorization(num: i64) -> i64 {
    if num < 10 {
        return num;
    }

    let mut n = num;
    let mut res: i64 = 0;
    let mut mult: i64 = 1;
    let mut d: i64 = 9;
    let mut overflow = false;

    while d >= 2 {
        let mut continuing = true;
        while continuing {
            if n % d == 0 && !overflow {
                n = n / d;
                if res + d * mult > 2147483647 {
                    overflow = true;
                } else {
                    res = res + d * mult;
                    mult = mult * 10;
                }
            } else {
                continuing = false;
            }
        }
        d = d - 1;
    }

    if overflow {
        return 0;
    }
    if n != 1 {
        return 0;
    }

    res
}
