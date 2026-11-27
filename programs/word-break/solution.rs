pub fn word_break(s: &[u8], wordDict: &[Vec<u8>]) -> bool {
    let n = s.len();

    let mut dp: Vec<bool> = Vec::new();
    let mut i = 0;
    while i <= n {
        dp.push(false);
        i += 1;
    }
    dp[0] = true;

    let mut end = 1;
    while end <= n {
        let mut w = 0;
        while w < wordDict.len() {
            let word = &wordDict[w];
            let len = word.len();

            if len <= end && dp[end - len] {
                let mut k = 0;
                let mut ok = true;

                while k < len {
                    if s[end - len + k] != word[k] {
                        ok = false;
                        break;
                    }
                    k += 1;
                }

                if ok {
                    dp[end] = true;
                    break;
                }
            }

            w += 1;
        }

        end += 1;
    }

    dp[n]
}
