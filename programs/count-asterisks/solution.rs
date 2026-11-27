pub fn count_asterisks(s: &[u8]) -> i64 {
    let mut count: i64 = 0;
    let mut inside: bool = false;
    let mut i: usize = 0;

    while i < s.len() {
        let c = s[i];
        if c == b'|' {
            inside = !inside;
        } else if c == b'*' {
            if !inside {
                count += 1;
            }
        }
        i += 1;
    }

    count
}
