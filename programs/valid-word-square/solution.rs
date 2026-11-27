pub fn valid_word_square(words: &[Vec<u8>]) -> bool {
    let n = words.len();
    let mut ok = true;
    let mut i = 0usize;
    while i < n {
        let row_len = words[i].len();
        let mut j = 0usize;
        while j < row_len {
            if j >= n {
                ok = false;
            } else if i >= words[j].len() {
                ok = false;
            } else if words[i][j] != words[j][i] {
                ok = false;
            }
            j += 1;
        }
        i += 1;
    }
    ok
}
