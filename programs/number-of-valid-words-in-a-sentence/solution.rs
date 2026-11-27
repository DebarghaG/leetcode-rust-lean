fn is_lowercase(c: u8) -> bool {
    c >= b'a' && c <= b'z'
}

fn is_valid_token(sentence: &[u8], start: usize, end: usize) -> bool {
    let mut hyphens: i64 = 0;
    let mut puncts: i64 = 0;
    let mut p: usize = start;

    while p < end {
        let c = sentence[p];

        if c >= b'0' && c <= b'9' {
            return false;
        } else if c == b'-' {
            hyphens += 1;
            if hyphens > 1 {
                return false;
            }
            if p == start || p + 1 >= end {
                return false;
            }

            let prev = sentence[p - 1];
            let next = sentence[p + 1];
            if !is_lowercase(prev) || !is_lowercase(next) {
                return false;
            }
        } else if c == b'!' || c == b'.' || c == b',' {
            puncts += 1;
            if puncts > 1 {
                return false;
            }
            if p + 1 != end {
                return false;
            }
        }

        p += 1;
    }

    true
}

pub fn count_valid_words(sentence: &[u8]) -> i64 {
    let n = sentence.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        while i < n && sentence[i] == b' ' {
            i += 1;
        }

        if i < n {
            let start = i;

            while i < n && sentence[i] != b' ' {
                i += 1;
            }

            let end = i;

            if is_valid_token(sentence, start, end) {
                count += 1;
            }
        }
    }

    count
}
