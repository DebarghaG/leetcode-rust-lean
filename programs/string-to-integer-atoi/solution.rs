pub fn my_atoi(s: &[u8]) -> i64 {
    let n = s.len();
    let mut i: usize = 0;

    while i < n && s[i] == b' ' {
        i += 1;
    }

    let mut sign: i64 = 1;
    if i < n {
        if s[i] == b'-' {
            sign = -1;
            i += 1;
        } else if s[i] == b'+' {
            i += 1;
        }
    }

    let limit: i64 = if sign < 0 { 2147483648 } else { 2147483647 };
    let mut result: i64 = 0;

    while i < n {
        let c = s[i];
        if c < b'0' || c > b'9' {
            break;
        }

        let digit: i64 = (c - b'0') as i64;

        if result > (limit - digit) / 10 {
            result = limit;
            break;
        }

        result = result * 10 + digit;
        i += 1;
    }

    sign * result
}
