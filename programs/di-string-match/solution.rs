pub fn di_string_match(s: &[u8]) -> Vec<i64> {
    let n: i64 = s.len() as i64;
    let mut low: i64 = 0;
    let mut high: i64 = n;
    let mut result: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < s.len() {
        if s[i] == b'I' {
            result.push(low);
            low += 1;
        } else {
            result.push(high);
            high -= 1;
        }
        i += 1;
    }

    result.push(low);
    result
}
