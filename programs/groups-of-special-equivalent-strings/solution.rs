pub fn num_special_equiv_groups(words: &[Vec<u8>]) -> i64 {
    let mut seen: Vec<Vec<i64>> = Vec::new();
    let mut groups: i64 = 0;

    let mut wi: usize = 0;
    while wi < words.len() {
        let mut sig: Vec<i64> = Vec::new();

        let mut k: usize = 0;
        while k < 52 {
            sig.push(0);
            k += 1;
        }

        let word = &words[wi];
        let mut ci: usize = 0;
        while ci < word.len() {
            let c: usize = (word[ci] as i64 - 97) as usize;
            if ci % 2 == 0 {
                sig[c] += 1;
            } else {
                sig[26 + c] += 1;
            }
            ci += 1;
        }

        let mut found: bool = false;
        let mut j: usize = 0;
        while j < seen.len() {
            let mut same: bool = true;
            let mut t: usize = 0;
            while t < 52 {
                if seen[j][t] != sig[t] {
                    same = false;
                }
                t += 1;
            }

            if same {
                found = true;
            }
            j += 1;
        }

        if !found {
            seen.push(sig);
            groups += 1;
        }

        wi += 1;
    }

    groups
}
