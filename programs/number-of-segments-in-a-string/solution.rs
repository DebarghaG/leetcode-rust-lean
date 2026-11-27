pub fn count_segments(s: &[u8]) -> i64 {
    let n: usize = s.len();
    let mut count: i64 = 0;
    // Flag: 1 means the previous character was a separator (start of string counts as one).
    let mut prev_sep: i64 = 1;
    let mut i: usize = 0;

    while i < n {
        let c: u8 = s[i];

        // Space (32), tab (9), LF (10), VT (11), FF (12), CR (13) are all <= 32.
        // Under the problem's alphabet no other character falls in this range.
        let cur_sep: i64 = if c <= 32u8 { 1 } else { 0 };

        if cur_sep == 0 {
            if prev_sep == 1 {
                count = count + 1;
            }
        }

        prev_sep = cur_sep;
        i = i + 1;
    }

    count
}
