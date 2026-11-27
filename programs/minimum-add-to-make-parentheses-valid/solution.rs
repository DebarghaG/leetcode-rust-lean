pub fn min_add_to_make_valid(s: &[u8]) -> i64 {
    let n: usize = s.len();
    let mut i: usize = 0;
    let mut open_needed: i64 = 0;
    let mut unmatched_open: i64 = 0;

    while i < n {
        if s[i] == b'(' {
            unmatched_open += 1;
        } else if s[i] == b')' {
            if unmatched_open > 0 {
                unmatched_open -= 1;
            } else {
                open_needed += 1;
            }
        }
        i += 1;
    }

    open_needed + unmatched_open
}
