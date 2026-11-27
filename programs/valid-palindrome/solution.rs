fn is_alnum(c: u8) -> bool {
    (c >= b'a' && c <= b'z')
        || (c >= b'A' && c <= b'Z')
        || (c >= b'0' && c <= b'9')
}

fn to_lower(c: u8) -> u8 {
    if c >= b'A' && c <= b'Z' {
        c + 32
    } else {
        c
    }
}

pub fn is_palindrome(s: &[u8]) -> bool {
    let n = s.len();
    if n == 0 {
        return true;
    }

    let mut i: usize = 0;
    let mut j: usize = n - 1;

    while i < j {
        while i < j && !is_alnum(s[i]) {
            i += 1;
        }
        while i < j && !is_alnum(s[j]) {
            j -= 1;
        }

        if i < j {
            let a = to_lower(s[i]);
            let b = to_lower(s[j]);

            if a != b {
                return false;
            }

            i += 1;
            j -= 1;
        }
    }

    true
}
