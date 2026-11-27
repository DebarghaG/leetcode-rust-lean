pub fn number_of_lines(widths: &[i64], s: &[u8]) -> Vec<i64> {
    let mut lines: i64 = 1;
    let mut current_width: i64 = 0;

    let mut i: usize = 0;
    while i < s.len() {
        let letter_index: usize = (s[i] - b'a') as usize;
        let width: i64 = widths[letter_index];

        if current_width + width > 100 {
            lines += 1;
            current_width = width;
        } else {
            current_width += width;
        }

        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    result.push(lines);
    result.push(current_width);
    result
}
