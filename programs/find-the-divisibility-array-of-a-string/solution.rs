pub fn divisibility_array(word: &[u8], m: i64) -> Vec<i64> {
    let n = word.len();
    let mut out: Vec<i64> = Vec::new();
    let mut rem: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let digit: i64 = (word[i] as i64) - 48;
        rem = (rem * 10 + digit) % m;

        if rem == 0 {
            out.push(1);
        } else {
            out.push(0);
        }

        i += 1;
    }

    out
}
