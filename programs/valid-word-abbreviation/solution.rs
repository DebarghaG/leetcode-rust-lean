pub fn valid_word_abbreviation(word: &[u8], abbr: &[u8]) -> bool {
    let n: usize = word.len();
    let m: usize = abbr.len();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while j < m {
        let c: u8 = abbr[j];

        if c >= b'0' && c <= b'9' {
            if c == b'0' {
                return false;
            }

            let mut num: i64 = 0;
            while j < m && abbr[j] >= b'0' && abbr[j] <= b'9' {
                num = num * 10 + (abbr[j] as i64 - 48);
                j += 1;
            }

            let remaining: i64 = (n - i) as i64;
            if num > remaining {
                return false;
            }

            i += num as usize;
        } else {
            if i >= n {
                return false;
            }
            if word[i] != c {
                return false;
            }
            i += 1;
            j += 1;
        }
    }

    i == n
}
