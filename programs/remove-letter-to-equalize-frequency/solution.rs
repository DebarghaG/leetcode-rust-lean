pub fn equal_frequency(word: &[u8]) -> bool {
    let n = word.len();
    let mut remove_at: usize = 0;

    while remove_at < n {
        let mut counts: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 26 {
            counts.push(0);
            k += 1;
        }

        let mut i: usize = 0;
        while i < n {
            if i != remove_at {
                let c: u8 = word[i];
                let idx: usize = (c - b'a') as usize;
                counts[idx] = counts[idx] + 1;
            }
            i += 1;
        }

        let mut target: i64 = -1;
        let mut good: bool = true;

        let mut j: usize = 0;
        while j < 26 {
            let f: i64 = counts[j];
            if f > 0 {
                if target < 0 {
                    target = f;
                } else if f != target {
                    good = false;
                }
            }
            j += 1;
        }

        if good {
            return true;
        }

        remove_at += 1;
    }

    false
}
