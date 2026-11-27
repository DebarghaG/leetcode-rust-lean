pub fn bitwise_complement(n: i64) -> i64 {
    if n == 0 {
        return 1;
    }

    let mut x = n;
    let mut mask: i64 = 0;

    while x > 0 {
        mask = mask * 2 + 1;
        x = x / 2;
    }

    mask - n
}
