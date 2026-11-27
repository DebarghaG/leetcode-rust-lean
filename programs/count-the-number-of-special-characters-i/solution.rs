pub fn number_of_special_chars(word: &[u8]) -> i64 {
    let mut lower: Vec<bool> = Vec::new();
    let mut upper: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        lower.push(false);
        upper.push(false);
        i += 1;
    }

    let mut pos: usize = 0;
    while pos < word.len() {
        let c = word[pos];

        if c >= b'a' && c <= b'z' {
            let idx = (c - b'a') as usize;
            lower[idx] = true;
        } else if c >= b'A' && c <= b'Z' {
            let idx = (c - b'A') as usize;
            upper[idx] = true;
        }

        pos += 1;
    }

    let mut count: i64 = 0;
    let mut j: usize = 0;
    while j < 26 {
        if lower[j] && upper[j] {
            count += 1;
        }
        j += 1;
    }

    count
}
