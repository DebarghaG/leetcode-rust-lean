pub fn minimized_string_length(s: &[u8]) -> i64 {
    let mut distinct: i64 = 0;
    let mut i: usize = 0;

    while i < s.len() {
        let c: u8 = s[i];
        let mut seen_before: bool = false;
        let mut j: usize = 0;

        while j < i {
            if s[j] == c {
                seen_before = true;
            }
            j += 1;
        }

        if !seen_before {
            distinct += 1;
        }

        i += 1;
    }

    distinct
}
