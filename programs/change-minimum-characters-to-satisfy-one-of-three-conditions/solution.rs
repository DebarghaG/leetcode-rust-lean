pub fn min_characters(a: &[u8], b: &[u8]) -> i64 {
    let mut ca: Vec<i64> = Vec::new();
    let mut cb: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < 26 {
        ca.push(0);
        cb.push(0);
        i += 1;
    }

    let mut len_a: i64 = 0;
    i = 0;
    while i < a.len() {
        let idx: usize = (a[i] - b'a') as usize;
        ca[idx] = ca[idx] + 1;
        len_a += 1;
        i += 1;
    }

    let mut len_b: i64 = 0;
    i = 0;
    while i < b.len() {
        let idx: usize = (b[i] - b'a') as usize;
        cb[idx] = cb[idx] + 1;
        len_b += 1;
        i += 1;
    }

    let mut best: i64 = len_a + len_b;

    // Condition 3: make all characters in both strings become the same letter.
    i = 0;
    while i < 26 {
        let cost: i64 = (len_a - ca[i]) + (len_b - cb[i]);
        if cost < best {
            best = cost;
        }
        i += 1;
    }

    // Conditions 1 and 2 using a split letter t.
    let mut t: usize = 0;
    while t < 25 {
        let mut cost1: i64 = 0; // a <= t and b > t
        let mut cost2: i64 = 0; // b <= t and a > t

        let mut j: usize = 0;
        while j < 26 {
            if j > t {
                cost1 = cost1 + ca[j];
                cost2 = cost2 + cb[j];
            } else {
                cost1 = cost1 + cb[j];
                cost2 = cost2 + ca[j];
            }
            j += 1;
        }

        if cost1 < best {
            best = cost1;
        }
        if cost2 < best {
            best = cost2;
        }

        t += 1;
    }

    best
}
