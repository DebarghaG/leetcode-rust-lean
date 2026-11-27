pub fn array_strings_are_equal(word1: &[Vec<u8>], word2: &[Vec<u8>]) -> bool {
    let mut s1: Vec<u8> = Vec::new();
    let mut i: usize = 0;

    while i < word1.len() {
        let word = &word1[i];
        let mut j: usize = 0;

        while j < word.len() {
            s1.push(word[j]);
            j += 1;
        }

        i += 1;
    }

    let mut s2: Vec<u8> = Vec::new();
    let mut i2: usize = 0;

    while i2 < word2.len() {
        let word = &word2[i2];
        let mut j2: usize = 0;

        while j2 < word.len() {
            s2.push(word[j2]);
            j2 += 1;
        }

        i2 += 1;
    }

    if s1.len() != s2.len() {
        return false;
    }

    let mut k: usize = 0;
    while k < s1.len() {
        if s1[k] != s2[k] {
            return false;
        }
        k += 1;
    }

    true
}
