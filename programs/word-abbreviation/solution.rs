fn digit_to_byte(d: usize) -> u8 {
    let mut result: u8 = b'0';
    if d == 1 {
        result = b'1';
    } else if d == 2 {
        result = b'2';
    } else if d == 3 {
        result = b'3';
    } else if d == 4 {
        result = b'4';
    } else if d == 5 {
        result = b'5';
    } else if d == 6 {
        result = b'6';
    } else if d == 7 {
        result = b'7';
    } else if d == 8 {
        result = b'8';
    } else if d == 9 {
        result = b'9';
    }
    result
}

pub fn words_abbreviation(words: &[Vec<u8>]) -> Vec<Vec<u8>> {
    let n: usize = words.len();
    let mut res: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let word = &words[i];
        let len: usize = word.len();

        let mut max_common: usize = 0;
        let mut j: usize = 0;

        while j < n {
            if j != i {
                let other = &words[j];
                if len > 0 && other.len() == len && other[len - 1] == word[len - 1] {
                    let mut k: usize = 0;
                    while k < len && word[k] == other[k] {
                        k += 1;
                    }
                    if k > max_common {
                        max_common = k;
                    }
                }
            }
            j += 1;
        }

        let p: usize = max_common + 1;

        if p + 2 < len {
            let mut ab: Vec<u8> = Vec::new();

            let mut k: usize = 0;
            while k < p {
                ab.push(word[k]);
                k += 1;
            }

            let count: usize = len - p - 1;
            let mut c: usize = count;
            let mut digits: Vec<u8> = Vec::new();

            if c == 0 {
                digits.push(b'0');
            } else {
                while c > 0 {
                    let d: usize = c % 10;
                    digits.push(digit_to_byte(d));
                    c = c / 10;
                }
            }

            let mut di: usize = digits.len();
            while di > 0 {
                di -= 1;
                ab.push(digits[di]);
            }

            ab.push(word[len - 1]);
            res.push(ab);
        } else {
            let mut copy: Vec<u8> = Vec::new();
            let mut k: usize = 0;
            while k < len {
                copy.push(word[k]);
                k += 1;
            }
            res.push(copy);
        }

        i += 1;
    }

    res
}
