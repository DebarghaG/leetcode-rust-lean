pub fn longest_awesome(s: &[u8]) -> i64 {
    let n = s.len();

    let mut first: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < 1024 {
        first.push(-1);
        j += 1;
    }
    first[0] = 0;

    let mut mask: usize = 0;
    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let digit: usize = (s[i] - b'0') as usize;
        mask = mask ^ (1usize << digit);

        let cur_len: i64 = (i + 1) as i64;

        let same = first[mask];
        if same >= 0 {
            let cand = cur_len - same;
            if cand > best {
                best = cand;
            }
        }

        let mut d: usize = 0;
        while d < 10 {
            let other = mask ^ (1usize << d);
            let prev = first[other];
            if prev >= 0 {
                let cand = cur_len - prev;
                if cand > best {
                    best = cand;
                }
            }
            d += 1;
        }

        if first[mask] == -1 {
            first[mask] = cur_len;
        }

        i += 1;
    }

    best
}
