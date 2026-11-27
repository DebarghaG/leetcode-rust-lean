pub fn broken_calc(startValue: i64, target: i64) -> i64 {
    let mut start = startValue;
    let mut t = target;

    if start >= t {
        return start - t;
    }

    let mut ops: i64 = 0;

    while t > start {
        if t % 2 == 0 {
            t = t / 2;
        } else {
            t = t + 1;
        }
        ops += 1;
    }

    ops + (start - t)
}
