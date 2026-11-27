fn gcd(mut x: i64, mut y: i64) -> i64 {
    while y != 0 {
        let t = x % y;
        x = y;
        y = t;
    }
    x
}

pub fn nth_magical_number(n: i64, a: i64, b: i64) -> i64 {
    let g = gcd(a, b);
    let lcm = (a / g) * b;

    let m = if a < b { a } else { b };
    let mut lo: i64 = 1;
    let mut hi: i64 = m * n;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let count = mid / a + mid / b - mid / lcm;

        if count >= n {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo % 1000000007
}
