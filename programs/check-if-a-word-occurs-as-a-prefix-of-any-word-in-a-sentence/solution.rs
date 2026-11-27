pub fn is_prefix_of_word(sentence: &[u8], searchWord: &[u8]) -> i64 {
    let n: usize = sentence.len();
    let m: usize = searchWord.len();

    let mut i: usize = 0;
    let mut word_index: i64 = 1;

    while i < n {
        let start: usize = i;

        while i < n && sentence[i] != b' ' {
            i += 1;
        }

        let word_len: usize = i - start;

        if word_len >= m {
            let mut j: usize = 0;
            let mut ok: bool = true;

            while j < m && ok {
                if sentence[start + j] != searchWord[j] {
                    ok = false;
                } else {
                    j += 1;
                }
            }

            if ok {
                return word_index;
            }
        }

        while i < n && sentence[i] == b' ' {
            i += 1;
        }

        word_index += 1;
    }

    -1
}
