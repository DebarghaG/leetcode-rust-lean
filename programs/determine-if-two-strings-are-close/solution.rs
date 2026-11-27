pub fn close_strings(word1: &[u8], word2: &[u8]) -> bool {
    let mut ok: bool = word1.len() == word2.len();

    let mut c1: Vec<i64> = Vec::new();
    let mut c2: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < 26 {
        c1.push(0);
        c2.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < word1.len() {
        let idx: usize = (word1[i] - b'a') as usize;
        c1[idx] += 1;
        i += 1;
    }

    i = 0;
    while i < word2.len() {
        let idx: usize = (word2[i] - b'a') as usize;
        c2[idx] += 1;
        i += 1;
    }

    i = 0;
    while i < 26 {
        let p1: bool = c1[i] > 0;
        let p2: bool = c2[i] > 0;
        if p1 != p2 {
            ok = false;
        }
        i += 1;
    }

    i = 0;
    while i < 26 {
        let mut j: usize = 0;
        while j + 1 < 26 {
            if c1[j] > c1[j + 1] {
                let t: i64 = c1[j];
                c1[j] = c1[j + 1];
                c1[j + 1] = t;
            }
            j += 1;
        }
        i += 1;
    }

    i = 0;
    while i < 26 {
        let mut j: usize = 0;
        while j + 1 < 26 {
            if c2[j] > c2[j + 1] {
                let t: i64 = c2[j];
                c2[j] = c2[j + 1];
                c2[j + 1] = t;
            }
            j += 1;
        }
        i += 1;
    }

    i = 0;
    while i < 26 {
        if c1[i] != c2[i] {
            ok = false;
        }
        i += 1;
    }

    ok
}
