pub fn minimum_boxes(n: i64) -> i64 {
    let mut remaining = n;
    let mut ans = 0i64;

    let mut h = 1i64;
    let mut layer = h * (h + 1) / 2;

    while remaining >= layer {
        remaining -= layer;
        ans += h;
        h += 1;
        layer = h * (h + 1) / 2;
    }

    let mut i = 1i64;
    while remaining > 0 {
        remaining -= i;
        ans += 1;
        i += 1;
    }

    ans
}
