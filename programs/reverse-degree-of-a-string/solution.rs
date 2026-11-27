pub fn reverse_degree(s: &[u8]) -> i64 {
    let n = s.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let c = s[i];
        let reverse_alphabet_index: i64 = (b'z' - c) as i64 + 1;
        let position_in_string: i64 = i as i64 + 1;
        total += reverse_alphabet_index * position_in_string;
        i += 1;
    }

    total
}
