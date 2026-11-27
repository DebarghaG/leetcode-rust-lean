pub fn find_complement(num: i64) -> i64 {
    if num == 0 {
        return 1;
    }

    let mut mask: i64 = 0;
    let mut x: i64 = num;

    while x > 0 {
        mask = (mask << 1) | 1;
        x = x >> 1;
    }

    num ^ mask
}
