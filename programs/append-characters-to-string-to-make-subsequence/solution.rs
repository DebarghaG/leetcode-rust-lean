pub fn append_characters(s: &[u8], t: &[u8]) -> i64 {
    let n = s.len();
    let m = t.len();

    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < n && j < m {
        if s[i] == t[j] {
            j += 1;
        }
        i += 1;
    }

    let mut result: i64 = 0;
    while j < m {
        result += 1;
        j += 1;
    }

    result
}
