fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn feasible(x: i64, divisor1: i64, divisor2: i64, unique_cnt1: i64, unique_cnt2: i64, lcm: i64) -> bool {
    let can1 = x - x / divisor1;
    let can2 = x - x / divisor2;
    let can_both = x - x / lcm;

    can1 >= unique_cnt1
        && can2 >= unique_cnt2
        && can_both >= unique_cnt1 + unique_cnt2
}

pub fn minimize_set(divisor1: i64, divisor2: i64, unique_cnt1: i64, unique_cnt2: i64) -> i64 {
    let g = gcd(divisor1, divisor2);
    let lcm = divisor1 / g * divisor2;

    let mut lo: i64 = 1;
    let mut hi: i64 = 4_000_000_000;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if feasible(mid, divisor1, divisor2, unique_cnt1, unique_cnt2, lcm) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    lo
}
