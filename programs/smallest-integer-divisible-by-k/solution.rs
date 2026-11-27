pub fn smallest_repunit_div_by_k(k: i64) -> i64 {
    if k % 2 == 0 || k % 5 == 0 {
        return -1;
    }

    let mut rem: i64 = 0;
    let mut length: i64 = 1;

    while length <= k {
        rem = (rem * 10 + 1) % k;

        if rem == 0 {
            return length;
        }

        length += 1;
    }

    -1
}
