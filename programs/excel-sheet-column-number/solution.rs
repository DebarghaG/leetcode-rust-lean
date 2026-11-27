pub fn title_to_number(columnTitle: &[u8]) -> i64 {
    let mut result: i64 = 0;
    let mut i: usize = 0;

    while i < columnTitle.len() {
        let c: u8 = columnTitle[i];
        let digit: i64 = (c as i64) - 64; // 'A' = 65, so 'A' -> 1
        result = result * 26 + digit;
        i = i + 1;
    }

    result
}
