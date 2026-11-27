pub fn count_vowels(word: &[u8]) -> i64 {
    let n: usize = word.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let c: u8 = word[i];
        if c == b'a' || c == b'e' || c == b'i' || c == b'o' || c == b'u' {
            let left: i64 = (i as i64) + 1;
            let right: i64 = (n - i) as i64;
            total = total + left * right;
        }
        i = i + 1;
    }

    total
}
