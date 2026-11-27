pub fn min_extra_char(s: &[u8], dictionary: &[Vec<u8>]) -> i64 {
    let n = s.len();
    let mut dp: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i <= n {
        dp.push(0);
        i += 1;
    }

    i = 1;
    while i <= n {
        let mut best = dp[i - 1] + 1;

        let mut d = 0usize;
        while d < dictionary.len() {
            let word_len = dictionary[d].len();

            if word_len <= i {
                let start = i - word_len;
                let mut matched = true;
                let mut j = 0usize;

                while j < word_len {
                    if s[start + j] != dictionary[d][j] {
                        matched = false;
                    }
                    j += 1;
                }

                if matched {
                    let candidate = dp[start];
                    if candidate < best {
                        best = candidate;
                    }
                }
            }

            d += 1;
        }

        dp[i] = best;
        i += 1;
    }

    dp[n]
}
