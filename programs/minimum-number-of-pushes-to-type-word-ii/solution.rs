pub fn minimum_pushes(word: &[u8]) -> i64 {
    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        freq.push(0);
        i += 1;
    }

    let n = word.len();
    let mut p: usize = 0;
    while p < n {
        let idx = (word[p] - b'a') as usize;
        freq[idx] = freq[idx] + 1;
        p += 1;
    }

    // Sort frequencies in descending order using selection sort.
    let mut a: usize = 0;
    while a < 26 {
        let mut max_idx: usize = a;
        let mut b: usize = a + 1;
        while b < 26 {
            if freq[b] > freq[max_idx] {
                max_idx = b;
            }
            b += 1;
        }

        let tmp = freq[a];
        freq[a] = freq[max_idx];
        freq[max_idx] = tmp;
        a += 1;
    }

    let mut total: i64 = 0;
    let mut k: usize = 0;
    while k < 26 {
        if freq[k] > 0 {
            let multiplier: i64 = (k as i64) / 8 + 1;
            total = total + freq[k] * multiplier;
        }
        k += 1;
    }

    total
}
