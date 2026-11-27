pub fn count_consistent_strings(allowed: &[u8], words: &[Vec<u8>]) -> i64 {
    let mut count: i64 = 0;
    let mut wi: usize = 0;

    while wi < words.len() {
        let word = &words[wi];
        let mut ok: bool = true;
        let mut ci: usize = 0;

        while ci < word.len() {
            let c: u8 = word[ci];
            let mut found: bool = false;
            let mut ai: usize = 0;

            while ai < allowed.len() {
                if allowed[ai] == c {
                    found = true;
                }
                ai += 1;
            }

            if !found {
                ok = false;
            }

            ci += 1;
        }

        if ok {
            count += 1;
        }

        wi += 1;
    }

    count
}
