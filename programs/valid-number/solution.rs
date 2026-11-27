pub fn is_number(s: &[u8]) -> bool {
    let n: usize = s.len();
    if n == 0 {
        return false;
    }

    let mut i: usize = 0;

    if s[i] == b'+' || s[i] == b'-' {
        i += 1;
    }

    let mut digits: usize = 0;

    while i < n && s[i] >= b'0' && s[i] <= b'9' {
        digits += 1;
        i += 1;
    }

    if i < n && s[i] == b'.' {
        i += 1;
        while i < n && s[i] >= b'0' && s[i] <= b'9' {
            digits += 1;
            i += 1;
        }
    }

    if digits == 0 {
        return false;
    }

    if i < n && (s[i] == b'e' || s[i] == b'E') {
        i += 1;

        if i < n && (s[i] == b'+' || s[i] == b'-') {
            i += 1;
        }

        let mut exp_digits: usize = 0;
        while i < n && s[i] >= b'0' && s[i] <= b'9' {
            exp_digits += 1;
            i += 1;
        }

        if exp_digits == 0 {
            return false;
        }
    }

    i == n
}
