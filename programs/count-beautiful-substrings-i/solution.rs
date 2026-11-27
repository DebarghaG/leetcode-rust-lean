fn is_vowel(c: u8) -> bool {
    c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u'
}

pub fn beautiful_substrings(s: &[u8], k: i64) -> i64 {
    let n = s.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut vowels: i64 = 0;
        let mut consonants: i64 = 0;
        let mut j: usize = i;

        while j < n {
            if is_vowel(s[j]) {
                vowels += 1;
            } else {
                consonants += 1;
            }

            if vowels == consonants && (vowels * consonants) % k == 0 {
                ans += 1;
            }

            j += 1;
        }

        i += 1;
    }

    ans
}
