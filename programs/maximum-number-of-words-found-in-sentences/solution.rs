pub fn most_words_found(sentences: &[Vec<u8>]) -> i64 {
    let mut max_words: i64 = 0;
    let mut i: usize = 0;

    while i < sentences.len() {
        let sentence = &sentences[i];
        let mut words: i64 = 1;
        let mut j: usize = 0;

        while j < sentence.len() {
            if sentence[j] == b' ' {
                words += 1;
            }
            j += 1;
        }

        if words > max_words {
            max_words = words;
        }

        i += 1;
    }

    max_words
}
