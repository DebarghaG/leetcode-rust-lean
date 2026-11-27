pub fn equal_substring(s: &[u8], t: &[u8], maxCost: i64) -> i64 {
    let n = s.len();
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut total: i64 = 0;
    let mut best: i64 = 0;

    while right < n {
        let a = s[right] as i64;
        let b = t[right] as i64;
        let d = if a >= b { a - b } else { b - a };
        total = total + d;

        while total > maxCost {
            let la = s[left] as i64;
            let lb = t[left] as i64;
            let ld = if la >= lb { la - lb } else { lb - la };
            total = total - ld;
            left = left + 1;
        }

        if left <= right {
            let len = (right - left + 1) as i64;
            if len > best {
                best = len;
            }
        }

        right = right + 1;
    }

    best
}
