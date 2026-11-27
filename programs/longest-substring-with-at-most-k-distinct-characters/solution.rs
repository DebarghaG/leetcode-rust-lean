pub fn length_of_longest_substring_k_distinct(s: &[u8], k: i64) -> i64 {
    if s.len() == 0 {
        return 0;
    }
    if k <= 0 {
        return 0;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 256 {
        counts.push(0);
        i += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut distinct: i64 = 0;
    let mut best: i64 = 0;

    while right < s.len() {
        let c: u8 = s[right];
        let idx: usize = c as usize;

        if counts[idx] == 0 {
            distinct += 1;
        }
        counts[idx] += 1;

        while distinct > k {
            let left_c: u8 = s[left];
            let left_idx: usize = left_c as usize;
            counts[left_idx] -= 1;
            if counts[left_idx] == 0 {
                distinct -= 1;
            }
            left += 1;
        }

        let len: i64 = (right - left + 1) as i64;
        if len > best {
            best = len;
        }

        right += 1;
    }

    best
}
