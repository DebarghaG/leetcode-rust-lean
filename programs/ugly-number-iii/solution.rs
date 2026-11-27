pub fn nth_ugly_number(n: i64, a: i64, b: i64, c: i64) -> i64 {
    let cap: i64 = 2_000_000_001;

    let ab = lcm_capped(a, b, cap);
    let ac = lcm_capped(a, c, cap);
    let bc = lcm_capped(b, c, cap);
    let abc = lcm_capped(ab, c, cap);

    let mut lo: i64 = 1;
    let mut hi: i64 = 2_000_000_000;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        let cnt = count_ugly(mid, a, b, c, ab, ac, bc, abc);

        if cnt >= n {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}

fn gcd(mut x: i64, mut y: i64) -> i64 {
    while y != 0 {
        let r = x % y;
        x = y;
        y = r;
    }
    x
}

fn lcm_capped(x: i64, y: i64, cap: i64) -> i64 {
    let g = gcd(x, y);
    let q = x / g;

    if q > cap / y {
        cap
    } else {
        q * y
    }
}

fn count_ugly(
    x: i64,
    a: i64,
    b: i64,
    c: i64,
    ab: i64,
    ac: i64,
    bc: i64,
    abc: i64,
) -> i64 {
    x / a + x / b + x / c - x / ab - x / ac - x / bc + x / abc
}
