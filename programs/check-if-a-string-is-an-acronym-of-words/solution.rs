pub fn is_acronym(words: &[Vec<u8>], s: &[u8]) -> bool {
    if words.len() != s.len() {
        return false;
    }

    let mut i: usize = 0;
    while i < words.len() {
        let word = &words[i];
        if word.len() == 0 {
            return false;
        }
        if word[0] != s[i] {
            return false;
        }
        i += 1;
    }

    true
}
