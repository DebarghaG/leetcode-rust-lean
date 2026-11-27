pub fn minimum_deletions(s: &[u8]) -> i64 {
    let n = s.len();

    let mut total_a: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if s[i] == b'a' {
            total_a += 1;
        }
        i += 1;
    }

    let mut best: i64 = total_a;
    let mut a_remaining: i64 = total_a;
    let mut b_seen: i64 = 0;

    i = 0;
    while i < n {
        if s[i] == b'a' {
            a_remaining -= 1;
        } else {
            b_seen += 1;
        }

        let cost = b_seen + a_remaining;
        if cost < best {
            best = cost;
        }

        i += 1;
    }

    best
}
