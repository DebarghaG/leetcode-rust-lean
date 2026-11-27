pub fn max_total_reward(rewardValues: &[i64]) -> i64 {
    let n = rewardValues.len();
    if n == 0 {
        return 0;
    }

    let mut maxv: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let x = rewardValues[i];
        if x > maxv {
            maxv = x;
        }
        i += 1;
    }

    let seen_len: usize = (maxv as usize) + 1;
    let mut seen: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < seen_len {
        seen.push(false);
        j += 1;
    }

    i = 0;
    while i < n {
        let x = rewardValues[i] as usize;
        seen[x] = true;
        i += 1;
    }

    let total_bits: i64 = 2 * maxv + 2;
    let word_count: usize = ((total_bits + 62) / 63) as usize;

    let mut dp: Vec<i64> = Vec::new();
    j = 0;
    while j < word_count {
        dp.push(0);
        j += 1;
    }
    dp[0] = 1;

    let mask63: i64 = 9223372036854775807;

    let mut v: i64 = 1;
    while v <= maxv {
        if seen[v as usize] {
            let q: usize = (v / 63) as usize;
            let r: usize = (v % 63) as usize;
            let source_words: usize = ((v + 62) / 63) as usize;

            let mut w: usize = 0;
            while w < source_words {
                let mut src: i64 = dp[w];

                if w + 1 == source_words {
                    let rem: usize = (v % 63) as usize;
                    if rem != 0 {
                        let mask: i64 = (1i64 << rem) - 1;
                        src = src & mask;
                    }
                }

                if src != 0 {
                    let dword: usize = w + q;

                    if r == 0 {
                        if dword < word_count {
                            dp[dword] = dp[dword] | src;
                        }
                    } else {
                        let low: i64 = (src << r) & mask63;
                        let high: i64 = src >> (63 - r);

                        if dword < word_count {
                            dp[dword] = dp[dword] | low;
                        }
                        if high != 0 && dword + 1 < word_count {
                            dp[dword + 1] = dp[dword + 1] | high;
                        }
                    }
                }

                w += 1;
            }
        }
        v += 1;
    }

    let mut result: i64 = 0;
    let mut found: bool = false;
    let mut wi: usize = word_count;
    while wi > 0 && !found {
        wi -= 1;
        let word: i64 = dp[wi];
        if word != 0 {
            let mut bit: usize = 63;
            while bit > 0 && !found {
                bit -= 1;
                let mask: i64 = 1i64 << bit;
                if (word & mask) != 0 {
                    result = (wi as i64) * 63 + (bit as i64);
                    found = true;
                }
            }
        }
    }

    result
}
