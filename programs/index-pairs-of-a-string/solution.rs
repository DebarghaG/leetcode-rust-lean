pub fn index_pairs(text: &[u8], words: &[Vec<u8>]) -> Vec<Vec<i64>> {
    let mut out: Vec<Vec<i64>> = Vec::new();
    let n = text.len();
    let m = words.len();

    let mut i = 0usize;
    while i < n {
        let mut j = i;
        while j < n {
            let len = j - i + 1;
            let mut matched = false;
            let mut k = 0usize;

            while k < m {
                let w = &words[k];
                if w.len() == len {
                    let mut t = 0usize;
                    let mut same = true;

                    while t < len {
                        if text[i + t] != w[t] {
                            same = false;
                            break;
                        }
                        t += 1;
                    }

                    if same {
                        matched = true;
                        break;
                    }
                }

                k += 1;
            }

            if matched {
                let mut pair: Vec<i64> = Vec::new();
                pair.push(i as i64);
                pair.push(j as i64);
                out.push(pair);
            }

            j += 1;
        }

        i += 1;
    }

    out
}
