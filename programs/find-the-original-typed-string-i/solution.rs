pub fn possible_string_count(word: &[u8]) -> i64 {
    let n = word.len();
    let mut runs: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        runs += 1;
        let current = word[i];
        i += 1;
        while i < n && word[i] == current {
            i += 1;
        }
    }

    1 + (n as i64) - runs
}
