pub fn find_words_containing(words: &[Vec<u8>], x: &[u8]) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();

    if x.len() == 0 {
        return result;
    }

    let target: u8 = x[0];
    let mut i: usize = 0;

    while i < words.len() {
        let word = &words[i];
        let mut j: usize = 0;
        let mut found: bool = false;

        while j < word.len() {
            if word[j] == target {
                found = true;
                break;
            }
            j += 1;
        }

        if found {
            result.push(i as i64);
        }

        i += 1;
    }

    result
}
