fn is_pal_base(x: i64, k: i64) -> bool {
    let mut y = x;
    let mut rev: i64 = 0;

    while y > 0 {
        rev = rev * k + (y % k);
        y = y / k;
    }

    rev == x
}

pub fn k_mirror(k: i64, n: i64) -> i64 {
    let mut sum: i64 = 0;
    let mut count: i64 = 0;

    let mut len: i64 = 1;
    let mut start: i64 = 1;
    let mut end: i64 = 10;

    while count < n {
        let mut half = start;

        while half < end && count < n {
            let mut p = half;
            let mut t = half;

            if len % 2 == 1 {
                t = half / 10;
            }

            while t > 0 {
                p = p * 10 + (t % 10);
                t = t / 10;
            }

            if is_pal_base(p, k) {
                sum = sum + p;
                count = count + 1;
            }

            half = half + 1;
        }

        len = len + 1;

        if len % 2 == 1 {
            start = start * 10;
            end = end * 10;
        }
    }

    sum
}
