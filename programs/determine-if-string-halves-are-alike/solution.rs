fn is_vowel(c: u8) -> bool {
    c == b'a'
        || c == b'e'
        || c == b'i'
        || c == b'o'
        || c == b'u'
        || c == b'A'
        || c == b'E'
        || c == b'I'
        || c == b'O'
        || c == b'U'
}

pub fn halves_are_alike(s: &[u8]) -> bool {
    let n = s.len();
    let half = n / 2;

    let mut i: usize = 0;
    let mut first_count: i64 = 0;
    let mut second_count: i64 = 0;

    while i < half {
        if is_vowel(s[i]) {
            first_count += 1;
        }
        if is_vowel(s[i + half]) {
            second_count += 1;
        }
        i += 1;
    }

    first_count == second_count
}
