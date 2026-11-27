pub fn check_if_pangram(sentence: &[u8]) -> bool {
    let mut seen: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        seen.push(false);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < sentence.len() {
        let c: u8 = sentence[idx];
        if c >= b'a' && c <= b'z' {
            let pos: usize = (c - b'a') as usize;
            seen[pos] = true;
        }
        idx += 1;
    }

    let mut j: usize = 0;
    while j < 26 {
        if !seen[j] {
            return false;
        }
        j += 1;
    }

    true
}
