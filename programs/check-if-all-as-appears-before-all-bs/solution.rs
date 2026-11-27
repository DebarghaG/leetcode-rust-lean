pub fn check_string(s: &[u8]) -> bool {
    let mut i: usize = 0;
    let mut seen_b: bool = false;

    while i < s.len() {
        if s[i] == b'b' {
            seen_b = true;
        } else if s[i] == b'a' && seen_b {
            return false;
        }
        i += 1;
    }

    true
}
