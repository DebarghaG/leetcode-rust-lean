pub fn does_alice_win(s: &[u8]) -> bool {
    let mut i: usize = 0;
    while i < s.len() {
        let c = s[i];
        if c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u' {
            return true;
        }
        i += 1;
    }
    false
}
