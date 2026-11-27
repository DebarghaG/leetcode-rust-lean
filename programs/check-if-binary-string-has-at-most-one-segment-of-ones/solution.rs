pub fn check_ones_segment(s: &[u8]) -> bool {
    let n = s.len();
    let mut segments: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'1' {
            if i == 0 || s[i - 1] != b'1' {
                segments += 1;
            }
        }
        i += 1;
    }

    segments <= 1
}
