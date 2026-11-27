pub fn string_matching(words: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let mut out: Vec<Vec<u8>> = Vec::new();
    let n = words.len();

    let mut i: usize = 0;
    while i < n {
        let needle_len = words[i].len();
        let mut is_sub = false;

        let mut j: usize = 0;
        while j < n {
            if i != j {
                let hay_len = words[j].len();
                if needle_len <= hay_len {
                    let mut start: usize = 0;
                    while start + needle_len <= hay_len {
                        let mut k: usize = 0;
                        let mut matched = true;

                        while k < needle_len {
                            if words[i][k] != words[j][start + k] {
                                matched = false;
                                break;
                            }
                            k += 1;
                        }

                        if matched {
                            is_sub = true;
                            break;
                        }

                        start += 1;
                    }
                }
            }

            if is_sub {
                break;
            }

            j += 1;
        }

        if is_sub {
            let mut row: Vec<u8> = Vec::new();
            let mut idx: usize = 0;
            while idx < needle_len {
                row.push(words[i][idx]);
                idx += 1;
            }
            out.push(row);
        }

        i += 1;
    }

    out
}
