pub fn first_uniq_char(s: &[u8]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < 26 {
        counts.push(0);
        i += 1;
    }

    let n = s.len();

    i = 0;
    while i < n {
        let c = (s[i] - b'a') as usize;
        counts[c] += 1;
        i += 1;
    }

    let mut j = 0;
    while j < n {
        let c = (s[j] - b'a') as usize;
        if counts[c] == 1 {
            return j as i64;
        }
        j += 1;
    }

    -1
}
