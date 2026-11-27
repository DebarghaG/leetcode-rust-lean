pub fn strong_password_checker(password: &[u8]) -> i64 {
    let n_usize: usize = password.len();

    let mut i: usize = 0;
    let mut has_lower: bool = false;
    let mut has_upper: bool = false;
    let mut has_digit: bool = false;

    while i < n_usize {
        let c: u8 = password[i];
        if c >= b'a' && c <= b'z' {
            has_lower = true;
        } else if c >= b'A' && c <= b'Z' {
            has_upper = true;
        } else if c >= b'0' && c <= b'9' {
            has_digit = true;
        }
        i += 1;
    }

    let mut missing: i64 = 0;
    if !has_lower {
        missing += 1;
    }
    if !has_upper {
        missing += 1;
    }
    if !has_digit {
        missing += 1;
    }

    let n: i64 = n_usize as i64;

    if n < 6 {
        let need_len: i64 = 6 - n;
        if need_len > missing {
            return need_len;
        }
        return missing;
    }

    let mut groups: Vec<i64> = Vec::new();
    i = 0;
    while i < n_usize {
        let mut j: usize = i + 1;
        while j < n_usize && password[j] == password[i] {
            j += 1;
        }
        let len: i64 = (j - i) as i64;
        if len >= 3 {
            groups.push(len);
        }
        i = j;
    }

    let mut replace: i64 = 0;
    let mut k: usize = 0;
    while k < groups.len() {
        replace += groups[k] / 3;
        k += 1;
    }

    if n <= 20 {
        if missing > replace {
            return missing;
        }
        return replace;
    }

    let mandatory_deletions: i64 = n - 20;
    let mut del: i64 = mandatory_deletions;

    k = 0;
    while k < groups.len() {
        if del > 0 && groups[k] % 3 == 0 {
            groups[k] = groups[k] - 1;
            del -= 1;
            replace -= 1;
        }
        k += 1;
    }

    k = 0;
    while k < groups.len() {
        if del >= 2 && groups[k] % 3 == 1 && groups[k] >= 4 {
            groups[k] = groups[k] - 2;
            del -= 2;
            replace -= 1;
        }
        k += 1;
    }

    while del >= 3 && replace > 0 {
        del -= 3;
        replace -= 1;
    }

    let best: i64 = if missing > replace {
        missing
    } else {
        replace
    };

    mandatory_deletions + best
}
