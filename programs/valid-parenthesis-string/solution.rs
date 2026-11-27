pub fn check_valid_string(s: &[u8]) -> bool {
    let mut min_open: i64 = 0;
    let mut max_open: i64 = 0;

    let n = s.len();
    for i in 0..n {
        let c = s[i];
        if c == b'(' {
            min_open += 1;
            max_open += 1;
        } else if c == b')' {
            min_open -= 1;
            max_open -= 1;
        } else {
            min_open -= 1;
            max_open += 1;
        }

        if min_open < 0 {
            min_open = 0;
        }

        if max_open < 0 {
            return false;
        }
    }

    min_open == 0
}
