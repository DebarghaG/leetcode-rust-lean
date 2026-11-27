pub fn bulb_switch(n: i64) -> i64 {
    if n <= 0 {
        return 0;
    }

    let mut r: i64 = 0;

    while (r + 1) * (r + 1) <= n {
        r += 1;
    }

    r
}
