pub fn score_of_string(s: &[u8]) -> i64 {
    let n = s.len();
    if n < 2 {
        return 0;
    }

    let mut score: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        let prev = s[i - 1] as i64;
        let curr = s[i] as i64;

        let mut diff = prev - curr;
        if diff < 0 {
            diff = -diff;
        }

        score += diff;
        i += 1;
    }

    score
}
