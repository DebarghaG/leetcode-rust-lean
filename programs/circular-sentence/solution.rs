pub fn is_circular_sentence(sentence: &[u8]) -> bool {
    let n = sentence.len();

    if n == 0 {
        return true;
    }

    let mut i: usize = 1;
    while i + 1 < n {
        if sentence[i] == b' ' {
            if sentence[i - 1] != sentence[i + 1] {
                return false;
            }
        }
        i += 1;
    }

    sentence[n - 1] == sentence[0]
}
