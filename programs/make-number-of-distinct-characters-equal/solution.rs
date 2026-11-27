pub fn is_it_possible(word1: &[u8], word2: &[u8]) -> bool {
    let mut cnt1: Vec<i64> = Vec::new();
    let mut cnt2: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        cnt1.push(0);
        cnt2.push(0);
        i += 1;
    }

    i = 0;
    while i < word1.len() {
        let idx: usize = (word1[i] as usize) - 97;
        cnt1[idx] = cnt1[idx] + 1;
        i += 1;
    }

    i = 0;
    while i < word2.len() {
        let idx: usize = (word2[i] as usize) - 97;
        cnt2[idx] = cnt2[idx] + 1;
        i += 1;
    }

    let mut distinct1: i64 = 0;
    let mut distinct2: i64 = 0;

    i = 0;
    while i < 26 {
        if cnt1[i] > 0 {
            distinct1 = distinct1 + 1;
        }
        if cnt2[i] > 0 {
            distinct2 = distinct2 + 1;
        }
        i += 1;
    }

    let mut found: bool = false;
    let mut c: usize = 0;
    while c < 26 {
        if cnt1[c] > 0 {
            let mut d: usize = 0;
            while d < 26 {
                if cnt2[d] > 0 {
                    if c == d {
                        if distinct1 == distinct2 {
                            found = true;
                        }
                    } else {
                        let mut new1: i64 = distinct1;
                        let mut new2: i64 = distinct2;

                        if cnt1[c] == 1 {
                            new1 = new1 - 1;
                        }
                        if cnt1[d] == 0 {
                            new1 = new1 + 1;
                        }

                        if cnt2[d] == 1 {
                            new2 = new2 - 1;
                        }
                        if cnt2[c] == 0 {
                            new2 = new2 + 1;
                        }

                        if new1 == new2 {
                            found = true;
                        }
                    }
                }
                d += 1;
            }
        }
        c += 1;
    }

    found
}
