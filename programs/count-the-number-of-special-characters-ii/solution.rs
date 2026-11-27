pub fn number_of_special_chars(word: &[u8]) -> i64 {
    let mut last_lower: Vec<i64> = Vec::new();
    let mut first_upper: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < 26 {
        last_lower.push(-1);
        first_upper.push(-1);
        k += 1;
    }

    let mut i: usize = 0;
    while i < word.len() {
        let b = word[i];

        if b >= b'a' && b <= b'z' {
            let idx: usize = (b - b'a') as usize;
            last_lower[idx] = i as i64;
        } else if b >= b'A' && b <= b'Z' {
            let idx: usize = (b - b'A') as usize;
            if first_upper[idx] == -1 {
                first_upper[idx] = i as i64;
            }
        }

        i += 1;
    }

    let mut count: i64 = 0;
    let mut j: usize = 0;
    while j < 26 {
        if last_lower[j] >= 0 && first_upper[j] >= 0 && last_lower[j] < first_upper[j] {
            count += 1;
        }
        j += 1;
    }

    count
}
