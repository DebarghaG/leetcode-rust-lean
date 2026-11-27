pub fn min_operations(s: &[u8]) -> i64 {
    let n = s.len();
    let mut i: usize = 0;
    let mut mismatches: i64 = 0;
    let mut total: i64 = 0;

    while i < n {
        let expected_zero: u8;
        if i % 2 == 0 {
            expected_zero = b'0';
        } else {
            expected_zero = b'1';
        }

        if s[i] != expected_zero {
            mismatches = mismatches + 1;
        }

        total = total + 1;
        i = i + 1;
    }

    let other = total - mismatches;
    if mismatches < other {
        mismatches
    } else {
        other
    }
}
