pub fn count_letters(s: &[u8]) -> i64 {
    let n = s.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let c = s[i];
        let mut j: usize = i + 1;

        while j < n && s[j] == c {
            j += 1;
        }

        let len: i64 = (j - i) as i64;
        total += len * (len + 1) / 2;
        i = j;
    }

    total
}
