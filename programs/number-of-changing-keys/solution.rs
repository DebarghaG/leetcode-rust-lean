pub fn count_key_changes(s: &[u8]) -> i64 {
    let n = s.len();
    if n == 0 {
        return 0;
    }

    let mut prev = s[0];
    if prev >= b'A' && prev <= b'Z' {
        prev = prev + 32;
    }

    let mut count: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        let mut cur = s[i];
        if cur >= b'A' && cur <= b'Z' {
            cur = cur + 32;
        }

        if cur != prev {
            count += 1;
        }

        prev = cur;
        i += 1;
    }

    count
}
