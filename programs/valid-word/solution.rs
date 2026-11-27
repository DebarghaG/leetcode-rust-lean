pub fn is_valid(word: &[u8]) -> bool {
    let n = word.len();
    if n < 3 {
        return false;
    }

    let mut has_vowel: bool = false;
    let mut has_consonant: bool = false;
    let mut has_invalid: bool = false;
    let mut i: usize = 0;

    while i < n {
        let c: u8 = word[i];

        let is_lower = c >= b'a' && c <= b'z';
        let is_upper = c >= b'A' && c <= b'Z';
        let is_digit = c >= b'0' && c <= b'9';
        let is_letter = is_lower || is_upper;

        if !is_letter && !is_digit {
            has_invalid = true;
        }

        if is_letter {
            if c == b'a'
                || c == b'e'
                || c == b'i'
                || c == b'o'
                || c == b'u'
                || c == b'A'
                || c == b'E'
                || c == b'I'
                || c == b'O'
                || c == b'U'
            {
                has_vowel = true;
            } else {
                has_consonant = true;
            }
        }

        i += 1;
    }

    !has_invalid && has_vowel && has_consonant
}
