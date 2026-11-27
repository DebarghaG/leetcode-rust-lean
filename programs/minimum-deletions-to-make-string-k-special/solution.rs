pub fn minimum_deletions(word: &[u8], k: i64) -> i64 {
    let mut cnt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        cnt.push(0);
        i = i + 1;
    }

    let n = word.len();
    i = 0;
    while i < n {
        let idx: usize = (word[i] - b'a') as usize;
        cnt[idx] = cnt[idx] + 1;
        i = i + 1;
    }

    if n == 0 {
        return 0;
    }

    let mut best: i64 = 1000000000;
    let mut a: usize = 0;
    while a < 26 {
        let base = cnt[a];
        if base > 0 {
            let cap = base + k;
            let mut deletions: i64 = 0;
            let mut b: usize = 0;
            while b < 26 {
                let c = cnt[b];
                if c < base {
                    deletions = deletions + c;
                } else if c > cap {
                    deletions = deletions + (c - cap);
                }
                b = b + 1;
            }
            if deletions < best {
                best = deletions;
            }
        }
        a = a + 1;
    }

    best
}
