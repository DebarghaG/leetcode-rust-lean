pub fn num_different_integers(word: &[u8]) -> i64 {
    let mut seen: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;

    while i < word.len() {
        if word[i] >= b'0' && word[i] <= b'9' {
            let run_start = i;

            while i < word.len() && word[i] >= b'0' && word[i] <= b'9' {
                i += 1;
            }

            let run_end = i;
            let mut digit_start = run_start;

            while digit_start < run_end && word[digit_start] == b'0' {
                digit_start += 1;
            }

            let mut num: Vec<u8> = Vec::new();

            if digit_start == run_end {
                num.push(b'0');
            } else {
                let mut k = digit_start;
                while k < run_end {
                    num.push(word[k]);
                    k += 1;
                }
            }

            let mut found: bool = false;
            let mut s: usize = 0;

            while s < seen.len() {
                if seen[s].len() == num.len() {
                    let mut same: bool = true;
                    let mut j: usize = 0;

                    while j < num.len() {
                        if seen[s][j] != num[j] {
                            same = false;
                        }
                        j += 1;
                    }

                    if same {
                        found = true;
                    }
                }

                s += 1;
            }

            if !found {
                seen.push(num);
            }
        } else {
            i += 1;
        }
    }

    seen.len() as i64
}
