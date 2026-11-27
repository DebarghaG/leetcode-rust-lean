pub fn num_of_strings(patterns: &[Vec<u8>], word: &[u8]) -> i64 {
    let n = patterns.len();
    let wlen = word.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let p = &patterns[i];
        let plen = p.len();
        let mut found: bool = false;

        if plen <= wlen {
            let mut start: usize = 0;
            while start + plen <= wlen {
                let mut j: usize = 0;
                let mut ok: bool = true;

                while j < plen {
                    if p[j] != word[start + j] {
                        ok = false;
                        break;
                    }
                    j += 1;
                }

                if ok {
                    found = true;
                    break;
                }

                start += 1;
            }
        }

        if found {
            count += 1;
        }

        i += 1;
    }

    count
}
