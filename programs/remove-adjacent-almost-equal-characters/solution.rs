pub fn remove_almost_equal_characters(word: &[u8]) -> i64 {
    let n = word.len();
    let mut ans: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        let a = word[i - 1] as i64;
        let b = word[i] as i64;
        let mut diff = b - a;
        if diff < 0 {
            diff = -diff;
        }

        if diff <= 1 {
            ans += 1;
            i += 2;
        } else {
            i += 1;
        }
    }

    ans
}
