fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    if a < 0 {
        -a
    } else {
        a
    }
}

pub fn can_measure_water(x: i64, y: i64, target: i64) -> bool {
    if target == 0 {
        return true;
    }
    if target > x + y {
        return false;
    }

    let g = gcd(x, y);
    target % g == 0
}
