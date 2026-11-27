fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    let n = haystack.len();
    let m = needle.len();

    if m == 0 {
        return true;
    }
    if m > n {
        return false;
    }

    let mut i: usize = 0;
    while i + m <= n {
        let mut j: usize = 0;
        let mut matched: bool = true;

        while j < m {
            if haystack[i + j] != needle[j] {
                matched = false;
                break;
            }
            j += 1;
        }

        if matched {
            return true;
        }

        i += 1;
    }

    false
}

pub fn max_repeating(sequence: &[u8], word: &[u8]) -> i64 {
    let w = word.len();
    if w == 0 {
        return 0;
    }

    let n = sequence.len();
    let max_k = n / w;

    let mut best: i64 = 0;
    let mut k: usize = 1;

    while k <= max_k {
        let mut pattern: Vec<u8> = Vec::new();

        let mut repeat: usize = 0;
        while repeat < k {
            let mut j: usize = 0;
            while j < w {
                pattern.push(word[j]);
                j += 1;
            }
            repeat += 1;
        }

        if contains(sequence, &pattern) {
            best = k as i64;
            k += 1;
        } else {
            break;
        }
    }

    best
}
