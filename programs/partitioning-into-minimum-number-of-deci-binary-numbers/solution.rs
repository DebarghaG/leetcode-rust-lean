pub fn min_partitions(n: &[u8]) -> i64 {
    let mut max_digit: u8 = 0;
    let mut i: usize = 0;

    while i < n.len() {
        let d: u8 = n[i] - b'0';
        if d > max_digit {
            max_digit = d;
        }
        i += 1;
    }

    max_digit as i64
}
