pub fn length_of_last_word(s: &[u8]) -> i64 {
    let mut i = s.len();
    let mut length: i64 = 0;

    while i > 0 {
        if s[i - 1] == b' ' {
            i -= 1;
        } else {
            break;
        }
    }

    while i > 0 {
        if s[i - 1] != b' ' {
            length += 1;
            i -= 1;
        } else {
            break;
        }
    }

    length
}
