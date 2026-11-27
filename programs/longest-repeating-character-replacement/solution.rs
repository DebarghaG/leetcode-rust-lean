pub fn character_replacement(s: &[u8], k: i64) -> i64 {
    let n = s.len();

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        counts.push(0);
        i += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut max_count: i64 = 0;
    let mut best: i64 = 0;

    while right < n {
        let idx: usize = (s[right] - b'A') as usize;
        counts[idx] = counts[idx] + 1;

        if counts[idx] > max_count {
            max_count = counts[idx];
        }

        let mut window_len: i64 = (right - left + 1) as i64;
        if window_len - max_count > k {
            let left_idx: usize = (s[left] - b'A') as usize;
            counts[left_idx] = counts[left_idx] - 1;
            left += 1;
        }

        window_len = (right - left + 1) as i64;
        if window_len > best {
            best = window_len;
        }

        right += 1;
    }

    best
}
