pub fn count_prefixes(words: &[Vec<u8>], s: &[u8]) -> i64 {
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < words.len() {
        let w = &words[i];
        let m = w.len();

        if m <= s.len() {
            let mut j: usize = 0;
            let mut ok: bool = true;

            while j < m && ok {
                if w[j] != s[j] {
                    ok = false;
                }
                j += 1;
            }

            if ok {
                count += 1;
            }
        }

        i += 1;
    }

    count
}
