pub fn hamming_weight(n: i64) -> i64 {
    let mut x = n;
    let mut count = 0i64;

    while x > 0 {
        count += x % 2;
        x = x / 2;
    }

    count
}
