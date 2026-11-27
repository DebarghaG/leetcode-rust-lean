pub fn find_the_longest_substring(s: &[u8]) -> i64 {
    let mut first: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 32 {
        first.push(-1);
        k += 1;
    }

    first[0] = 0;

    let mut mask: usize = 0;
    let mut best: i64 = 0;
    let mut i: usize = 0;
    let n = s.len();

    while i < n {
        let c = s[i];

        if c == b'a' {
            mask = mask ^ 1;
        } else if c == b'e' {
            mask = mask ^ 2;
        } else if c == b'i' {
            mask = mask ^ 4;
        } else if c == b'o' {
            mask = mask ^ 8;
        } else if c == b'u' {
            mask = mask ^ 16;
        }

        let pos = (i + 1) as i64;
        let prev = first[mask];

        if prev == -1 {
            first[mask] = pos;
        } else {
            let len = pos - prev;
            if len > best {
                best = len;
            }
        }

        i += 1;
    }

    best
}
