pub fn can_construct(s: &[u8], k: i64) -> bool {
    let n = s.len() as i64;
    if k > n {
        return false;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < 26 {
        counts.push(0);
        i += 1;
    }

    let mut pos = 0;
    while pos < s.len() {
        let idx = (s[pos] - b'a') as usize;
        counts[idx] = counts[idx] + 1;
        pos += 1;
    }

    let mut odd_count: i64 = 0;
    let mut j = 0;
    while j < 26 {
        if counts[j] % 2 == 1 {
            odd_count += 1;
        }
        j += 1;
    }

    odd_count <= k
}
