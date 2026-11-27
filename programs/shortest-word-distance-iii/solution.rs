fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn word_eq_vec(w: &Vec<u8>, target: &[u8]) -> bool {
    if w.len() != target.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < w.len() {
        if w[i] != target[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn shortest_word_distance(wordsDict: &[Vec<u8>], word1: &[u8], word2: &[u8]) -> i64 {
    let n: usize = wordsDict.len();
    let mut best: i64 = n as i64 + 1;

    if bytes_eq(word1, word2) {
        let mut last: i64 = -1;
        let mut i: usize = 0;
        while i < n {
            if word_eq_vec(&wordsDict[i], word1) {
                if last >= 0 {
                    let diff: i64 = i as i64 - last;
                    if diff < best {
                        best = diff;
                    }
                }
                last = i as i64;
            }
            i += 1;
        }
    } else {
        let mut p1: i64 = -1;
        let mut p2: i64 = -1;
        let mut i: usize = 0;
        while i < n {
            if word_eq_vec(&wordsDict[i], word1) {
                p1 = i as i64;
                if p2 >= 0 {
                    let mut diff: i64 = p1 - p2;
                    if diff < 0 {
                        diff = -diff;
                    }
                    if diff < best {
                        best = diff;
                    }
                }
            }
            if word_eq_vec(&wordsDict[i], word2) {
                p2 = i as i64;
                if p1 >= 0 {
                    let mut diff: i64 = p2 - p1;
                    if diff < 0 {
                        diff = -diff;
                    }
                    if diff < best {
                        best = diff;
                    }
                }
            }
            i += 1;
        }
    }

    best
}
