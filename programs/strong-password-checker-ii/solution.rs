pub fn strong_password_checker_ii(password: &[u8]) -> bool {
    let n = password.len();
    if n < 8 {
        return false;
    }

    let mut has_lower = false;
    let mut has_upper = false;
    let mut has_digit = false;
    let mut has_special = false;

    let mut i: usize = 0;
    while i < n {
        let c = password[i];

        if c >= b'a' && c <= b'z' {
            has_lower = true;
        }
        if c >= b'A' && c <= b'Z' {
            has_upper = true;
        }
        if c >= b'0' && c <= b'9' {
            has_digit = true;
        }
        if c == b'!'
            || c == b'@'
            || c == b'#'
            || c == b'$'
            || c == b'%'
            || c == b'^'
            || c == b'&'
            || c == b'*'
            || c == b'('
            || c == b')'
            || c == b'-'
            || c == b'+'
        {
            has_special = true;
        }

        if i > 0 {
            if password[i] == password[i - 1] {
                return false;
            }
        }

        i += 1;
    }

    has_lower && has_upper && has_digit && has_special
}
