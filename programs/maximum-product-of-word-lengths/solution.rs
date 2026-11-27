pub fn max_product(words: &[Vec<u8>]) -> i64 {
    let n = words.len();

    let mut masks: Vec<i64> = Vec::new();
    let mut lens: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let word = &words[i];
        let mut mask: i64 = 0;

        let mut k = 0;
        while k < word.len() {
            let c = word[k];
            let idx: i64 = (c as i64) - 97;
            let bit: i64 = 1i64 << idx;
            mask = mask | bit;
            k += 1;
        }

        masks.push(mask);
        lens.push(word.len() as i64);
        i += 1;
    }

    let mut best: i64 = 0;

    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            if (masks[i] & masks[j]) == 0 {
                let product = lens[i] * lens[j];
                if product > best {
                    best = product;
                }
            }
            j += 1;
        }
        i += 1;
    }

    best
}
