pub fn min_deletions(s: &[u8]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        counts.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < s.len() {
        let b = s[idx];
        let mut c: usize = 0;
        let mut letter: u8 = b'a';
        while c < 26 {
            if b == letter {
                counts[c] += 1;
            }
            c += 1;
            letter += 1;
        }
        idx += 1;
    }

    let mut freqs: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        if counts[k] > 0 {
            freqs.push(counts[k]);
        }
        k += 1;
    }

    let n = freqs.len();
    let mut a: usize = 1;
    while a < n {
        let key = freqs[a];
        let mut j: usize = a;
        while j > 0 {
            if freqs[j - 1] < key {
                freqs[j] = freqs[j - 1];
                j -= 1;
            } else {
                break;
            }
        }
        freqs[j] = key;
        a += 1;
    }

    let mut deletions: i64 = 0;
    let mut max_allowed: i64 = 1000000000;
    let mut p: usize = 0;
    while p < n {
        let f = freqs[p];
        if max_allowed > 0 {
            let take = if f < max_allowed { f } else { max_allowed };
            deletions += f - take;
            max_allowed = take - 1;
        } else {
            deletions += f;
        }
        p += 1;
    }

    deletions
}
