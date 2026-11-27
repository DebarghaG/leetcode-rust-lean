pub fn divide(dividend: i64, divisor: i64) -> i64 {
    let mut negative: bool = false;
    if dividend < 0 {
        if divisor > 0 {
            negative = true;
        }
    } else {
        if divisor < 0 {
            negative = true;
        }
    }

    let mut a: i64 = dividend;
    if a < 0 {
        a = -a;
    }

    let mut b: i64 = divisor;
    if b < 0 {
        b = -b;
    }

    let mut q: i64 = 0;
    let mut shift: usize = 32;
    while shift > 0 {
        shift = shift - 1;
        let shifted: i64 = b << shift;
        if shifted <= a {
            a = a - shifted;
            q = q + (1i64 << shift);
        }
    }

    let result: i64 = if negative { -q } else { q };

    if result > 2147483647i64 {
        2147483647i64
    } else if result < -2147483648i64 {
        -2147483648i64
    } else {
        result
    }
}
