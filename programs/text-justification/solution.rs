pub fn full_justify(words: &[Vec<u8>], maxWidth: i64) -> Vec<Vec<u8>> {
    let n = words.len();
    let mut result: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i;
        let mut total_chars: i64 = 0;

        while j < n {
            let wlen = words[j].len() as i64;
            if j > i {
                let spaces = (j - i) as i64;
                if total_chars + spaces + wlen > maxWidth {
                    break;
                }
            }
            total_chars += wlen;
            j += 1;
        }

        let mut line: Vec<u8> = Vec::new();
        let count = j - i;

        if j == n || count == 1 {
            let mut k = i;
            while k < j {
                if k > i {
                    line.push(b' ');
                }

                let wlen = words[k].len();
                let mut p = 0;
                while p < wlen {
                    line.push(words[k][p]);
                    p += 1;
                }

                k += 1;
            }

            while (line.len() as i64) < maxWidth {
                line.push(b' ');
            }
        } else {
            let gaps = count - 1;
            let spaces_total = maxWidth - total_chars;
            let base = spaces_total / (gaps as i64);
            let extra = spaces_total % (gaps as i64);

            let mut k = i;
            while k < j {
                let wlen = words[k].len();
                let mut p = 0;
                while p < wlen {
                    line.push(words[k][p]);
                    p += 1;
                }

                if k < j - 1 {
                    let mut s: i64 = 0;
                    while s < base {
                        line.push(b' ');
                        s += 1;
                    }

                    if ((k - i) as i64) < extra {
                        line.push(b' ');
                    }
                }

                k += 1;
            }
        }

        result.push(line);
        i = j;
    }

    result
}
