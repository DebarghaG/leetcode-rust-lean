pub fn binary_gap(n: i64) -> i64 {
    let mut m = n;
    let mut pos = 0i64;
    let mut last = -1i64;
    let mut best = 0i64;

    while m > 0 {
        if m % 2 == 1 {
            if last >= 0 {
                let distance = pos - last;
                if distance > best {
                    best = distance;
                }
            }
            last = pos;
        }
        m = m / 2;
        pos = pos + 1;
    }

    best
}
