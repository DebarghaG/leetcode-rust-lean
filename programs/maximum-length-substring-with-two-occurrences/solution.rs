pub fn maximum_length_substring(s: &[u8]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        counts.push(0);
        i = i + 1;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut best: i64 = 0;

    while right < s.len() {
        let c: usize = (s[right] - b'a') as usize;
        counts[c] = counts[c] + 1;

        while counts[c] > 2 {
            let d: usize = (s[left] - b'a') as usize;
            counts[d] = counts[d] - 1;
            left = left + 1;
        }

        let current: i64 = (right - left + 1) as i64;
        if current > best {
            best = current;
        }

        right = right + 1;
    }

    best
}
