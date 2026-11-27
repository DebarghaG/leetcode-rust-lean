pub fn percentage_letter(s: &[u8], letter: &[u8]) -> i64 {
    let target: u8 = letter[0];
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < s.len() {
        if s[i] == target {
            count += 1;
        }
        i += 1;
    }

    count * 100 / (s.len() as i64)
}
