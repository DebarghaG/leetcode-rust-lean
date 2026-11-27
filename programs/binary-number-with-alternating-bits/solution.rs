pub fn has_alternating_bits(n: i64) -> bool {
    let mut x: i64 = n;
    let mut prev: i64 = x % 2;
    x = x / 2;

    while x > 0 {
        let cur: i64 = x % 2;
        if cur == prev {
            return false;
        }
        prev = cur;
        x = x / 2;
    }

    true
}
