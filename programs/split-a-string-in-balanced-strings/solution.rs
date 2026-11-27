pub fn balanced_string_split(s: &[u8]) -> i64 {
    let n = s.len();
    let mut balance: i64 = 0;
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if s[i] == b'L' {
            balance = balance + 1;
        } else {
            balance = balance - 1;
        }
        if balance == 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
