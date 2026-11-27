pub fn query_string(s: &[u8], n: i64) -> bool {
    if n < 1 {
        return true;
    }

    // To contain all numbers up to n >= 2048, s would need to contain
    // all 1024 distinct 10-bit binary strings. Since s.len() <= 1000,
    // this is impossible.
    if n >= 2048 {
        return false;
    }

    // Convert n to usize without casts.
    let mut limit: usize = 0;
    let mut t: i64 = 0;
    while t < n {
        limit += 1;
        t += 1;
    }

    let mut seen: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i <= limit {
        seen.push(false);
        i += 1;
    }

    let mut start: usize = 0;
    while start < s.len() {
        let mut end: usize = start;
        let mut val: usize = 0;
        let mut count: usize = 0;

        // n < 2048, so every relevant binary representation has length <= 11.
        while end < s.len() && count < 11 {
            val = val * 2;
            if s[end] == b'1' {
                val += 1;
            }
            end += 1;
            count += 1;

            if val >= 1 && val <= limit {
                seen[val] = true;
            }
            if val > limit {
                break;
            }
        }

        start += 1;
    }

    let mut x: usize = 1;
    while x <= limit {
        if !seen[x] {
            return false;
        }
        x += 1;
    }

    true
}
