pub fn minimum_length_encoding(words: &[Vec<u8>]) -> i64 {
    let n = words.len();

    let mut keep: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        keep.push(true);
        i += 1;
    }

    i = 0;
    while i < n {
        let mut j = 0;
        while j < n {
            if i != j {
                let li = words[i].len();
                let lj = words[j].len();

                if li < lj {
                    let offset = lj - li;
                    let mut k = 0;
                    let mut is_suffix = true;
                    while k < li {
                        if words[i][k] != words[j][offset + k] {
                            is_suffix = false;
                        }
                        k += 1;
                    }
                    if is_suffix {
                        keep[i] = false;
                    }
                } else if li == lj && j < i {
                    let mut k = 0;
                    let mut same = true;
                    while k < li {
                        if words[i][k] != words[j][k] {
                            same = false;
                        }
                        k += 1;
                    }
                    if same {
                        keep[i] = false;
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        if keep[i] {
            ans += (words[i].len() as i64) + 1;
        }
        i += 1;
    }

    ans
}
