pub fn calculate_score(s: &[u8]) -> i64 {
    let mut stacks: Vec<Vec<i64>> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        stacks.push(Vec::new());
        k += 1;
    }

    let mut score: i64 = 0;
    let n: usize = s.len();
    let mut i: usize = 0;

    while i < n {
        let idx: usize = (s[i] - b'a') as usize;
        let mirror: usize = 25 - idx;

        if stacks[mirror].len() > 0 {
            let top: usize = stacks[mirror].len() - 1;
            let j: i64 = stacks[mirror][top];
            stacks[mirror].pop();
            score = score + (i as i64 - j);
        } else {
            stacks[idx].push(i as i64);
        }

        i += 1;
    }

    score
}
