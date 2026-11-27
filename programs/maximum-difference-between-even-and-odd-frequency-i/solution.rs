pub fn max_difference(s: &[u8]) -> i64 {
    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        freq.push(0);
        i += 1;
    }

    i = 0;
    while i < s.len() {
        let idx: usize = (s[i] - b'a') as usize;
        freq[idx] = freq[idx] + 1;
        i += 1;
    }

    let mut max_odd: i64 = -1;
    let mut min_even: i64 = 1000;

    i = 0;
    while i < 26 {
        let f: i64 = freq[i];
        if f > 0 {
            if f % 2 == 1 {
                if f > max_odd {
                    max_odd = f;
                }
            } else {
                if f < min_even {
                    min_even = f;
                }
            }
        }
        i += 1;
    }

    // If no character has an odd frequency, treat the odd contribution as 0.
    if max_odd < 0 {
        max_odd = 0;
    }
    // If no character has an even frequency (should not happen per constraints),
    // treat the even contribution as 0 to avoid a huge negative sentinel.
    if min_even == 1000 {
        min_even = 0;
    }

    max_odd - min_even
}
