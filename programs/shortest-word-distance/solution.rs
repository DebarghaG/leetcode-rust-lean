fn bytes_eq(a: &Vec<u8>, b: &[u8]) -> bool {
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

pub fn shortest_distance(wordsDict: &[Vec<u8>], word1: &[u8], word2: &[u8]) -> i64 {
    let mut last1: i64 = -1;
    let mut last2: i64 = -1;
    let mut best: i64 = 1000000000;

    let n = wordsDict.len();
    let mut i: usize = 0;

    while i < n {
        let is1 = bytes_eq(&wordsDict[i], word1);
        let is2 = bytes_eq(&wordsDict[i], word2);
        let pos = i as i64;

        if is1 {
            last1 = pos;
            if last2 >= 0 {
                let mut diff = last1 - last2;
                if diff < 0 {
                    diff = -diff;
                }
                if diff < best {
                    best = diff;
                }
            }
        }

        if is2 {
            last2 = pos;
            if last1 >= 0 {
                let mut diff = last2 - last1;
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

    best
}
