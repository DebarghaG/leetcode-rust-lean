pub fn length_of_longest_substring(s: &[u8]) -> i64 {
    let n = s.len();

    // last[c] stores the most recent index of byte c, or -1 if unseen.
    let mut last: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 256 {
        last.push(-1);
        i += 1;
    }

    let mut best: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;

    while right < n {
        let idx: usize = s[right] as usize;
        let prev: i64 = last[idx];

        if prev >= left as i64 {
            left = (prev + 1) as usize;
        }

        last[idx] = right as i64;

        let cur: i64 = (right - left + 1) as i64;
        if cur > best {
            best = cur;
        }

        right += 1;
    }

    best
}
