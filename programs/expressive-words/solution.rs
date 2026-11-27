fn is_stretchy(s: &[u8], w: &[u8]) -> bool {
    let n = s.len();
    let m = w.len();
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < n && j < m {
        if s[i] != w[j] {
            return false;
        }

        let ch = s[i];

        let mut i2 = i;
        while i2 < n && s[i2] == ch {
            i2 += 1;
        }

        let mut j2 = j;
        while j2 < m && w[j2] == ch {
            j2 += 1;
        }

        let count_s = i2 - i;
        let count_w = j2 - j;

        if count_s < count_w {
            return false;
        }
        if count_s != count_w && count_s < 3 {
            return false;
        }

        i = i2;
        j = j2;
    }

    i == n && j == m
}

pub fn expressive_words(s: &[u8], words: &[Vec<u8>]) -> i64 {
    let mut count: i64 = 0;
    let mut k: usize = 0;

    while k < words.len() {
        let word: &[u8] = &words[k];
        if is_stretchy(s, word) {
            count += 1;
        }
        k += 1;
    }

    count
}
