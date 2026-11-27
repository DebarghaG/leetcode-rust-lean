fn roman_value(c: u8) -> i64 {
    if c == b'I' {
        1
    } else if c == b'V' {
        5
    } else if c == b'X' {
        10
    } else if c == b'L' {
        50
    } else if c == b'C' {
        100
    } else if c == b'D' {
        500
    } else if c == b'M' {
        1000
    } else {
        0
    }
}

pub fn roman_to_int(s: &[u8]) -> i64 {
    let n = s.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let cur = roman_value(s[i]);
        if i + 1 < n {
            let next = roman_value(s[i + 1]);
            if cur < next {
                total = total - cur;
            } else {
                total = total + cur;
            }
        } else {
            total = total + cur;
        }
        i = i + 1;
    }

    total
}
