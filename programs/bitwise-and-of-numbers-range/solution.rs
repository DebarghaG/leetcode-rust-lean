pub fn range_bitwise_and(left: i64, right: i64) -> i64 {
    let mut l = left;
    let mut r = right;
    let mut shift: i64 = 0;

    while l < r {
        l = l >> 1;
        r = r >> 1;
        shift = shift + 1;
    }

    l << shift
}
