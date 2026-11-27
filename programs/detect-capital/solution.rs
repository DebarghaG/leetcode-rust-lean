pub fn detect_capital_use(word: &[u8]) -> bool {
    let n = word.len();
    if n == 0 {
        return true;
    }

    let mut upper_count: usize = 0;
    let mut i: usize = 0;
    while i < n {
        let c = word[i];
        if c >= b'A' && c <= b'Z' {
            upper_count += 1;
        }
        i += 1;
    }

    let first_upper = word[0] >= b'A' && word[0] <= b'Z';

    if upper_count == 0 {
        return true;
    }
    if upper_count == n {
        return true;
    }
    if first_upper && upper_count == 1 {
        return true;
    }

    false
}
