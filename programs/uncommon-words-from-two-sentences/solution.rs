pub fn uncommon_from_sentences(s1: &[u8], s2: &[u8]) -> Vec<Vec<u8>> {
    let w1 = split_words(s1);
    let w2 = split_words(s2);

    let mut out: Vec<Vec<u8>> = Vec::new();

    let mut i: usize = 0;
    while i < w1.len() {
        let mut count: i64 = 0;

        let mut j: usize = 0;
        while j < w1.len() {
            if w1[i].len() == w1[j].len() {
                let mut eq: bool = true;
                let mut t: usize = 0;
                while t < w1[i].len() {
                    if w1[i][t] != w1[j][t] {
                        eq = false;
                    }
                    t = t + 1;
                }
                if eq {
                    count = count + 1;
                }
            }
            j = j + 1;
        }

        let mut j2: usize = 0;
        while j2 < w2.len() {
            if w1[i].len() == w2[j2].len() {
                let mut eq: bool = true;
                let mut t: usize = 0;
                while t < w1[i].len() {
                    if w1[i][t] != w2[j2][t] {
                        eq = false;
                    }
                    t = t + 1;
                }
                if eq {
                    count = count + 1;
                }
            }
            j2 = j2 + 1;
        }

        if count == 1 {
            let mut word: Vec<u8> = Vec::new();
            let mut k: usize = 0;
            while k < w1[i].len() {
                word.push(w1[i][k]);
                k = k + 1;
            }
            out.push(word);
        }

        i = i + 1;
    }

    let mut i2: usize = 0;
    while i2 < w2.len() {
        let mut count: i64 = 0;

        let mut j: usize = 0;
        while j < w1.len() {
            if w2[i2].len() == w1[j].len() {
                let mut eq: bool = true;
                let mut t: usize = 0;
                while t < w2[i2].len() {
                    if w2[i2][t] != w1[j][t] {
                        eq = false;
                    }
                    t = t + 1;
                }
                if eq {
                    count = count + 1;
                }
            }
            j = j + 1;
        }

        let mut j2: usize = 0;
        while j2 < w2.len() {
            if w2[i2].len() == w2[j2].len() {
                let mut eq: bool = true;
                let mut t: usize = 0;
                while t < w2[i2].len() {
                    if w2[i2][t] != w2[j2][t] {
                        eq = false;
                    }
                    t = t + 1;
                }
                if eq {
                    count = count + 1;
                }
            }
            j2 = j2 + 1;
        }

        if count == 1 {
            let mut word: Vec<u8> = Vec::new();
            let mut k: usize = 0;
            while k < w2[i2].len() {
                word.push(w2[i2][k]);
                k = k + 1;
            }
            out.push(word);
        }

        i2 = i2 + 1;
    }

    out
}

fn split_words(s: &[u8]) -> Vec<Vec<u8>> {
    let mut words: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();

    let mut i: usize = 0;
    while i < s.len() {
        if s[i] == b' ' {
            if cur.len() > 0 {
                words.push(cur);
                cur = Vec::new();
            }
        } else {
            cur.push(s[i]);
        }
        i = i + 1;
    }

    if cur.len() > 0 {
        words.push(cur);
    }

    words
}
