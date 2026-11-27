pub fn score_of_parentheses(s: &[u8]) -> i64 {
    let mut score: i64 = 0;
    let mut depth: i64 = 0;
    let mut i: usize = 0;

    while i < s.len() {
        if s[i] == b'(' {
            depth += 1;
        } else {
            depth -= 1;
            if i > 0 && s[i - 1] == b'(' {
                let mut add: i64 = 1;
                let mut k: i64 = 0;
                while k < depth {
                    add *= 2;
                    k += 1;
                }
                score += add;
            }
        }
        i += 1;
    }

    score
}
