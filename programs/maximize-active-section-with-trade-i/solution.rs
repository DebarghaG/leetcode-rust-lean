pub fn max_active_sections_after_trade(s: &[u8]) -> i64 {
    let n = s.len();

    let mut total: i64 = 0;
    let mut i = 0;
    while i < n {
        if s[i] == b'1' {
            total += 1;
        }
        i += 1;
    }

    let m = n + 2;
    let mut t: Vec<u8> = Vec::new();
    t.push(b'1');

    i = 0;
    while i < n {
        t.push(s[i]);
        i += 1;
    }

    t.push(b'1');

    let mut lens: Vec<i64> = Vec::new();
    let mut is_one: Vec<bool> = Vec::new();

    let mut p = 0;
    while p < m {
        let mut q = p + 1;
        while q < m && t[q] == t[p] {
            q += 1;
        }

        lens.push((q - p) as i64);
        if t[p] == b'1' {
            is_one.push(true);
        } else {
            is_one.push(false);
        }

        p = q;
    }

    let mut best: i64 = 0;
    let mut r = 0;
    while r < lens.len() {
        if is_one[r] && r > 0 && r + 1 < lens.len() {
            let gain = lens[r - 1] + lens[r + 1];
            if gain > best {
                best = gain;
            }
        }
        r += 1;
    }

    total + best
}
