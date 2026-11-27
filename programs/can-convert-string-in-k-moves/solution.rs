pub fn can_convert_string(s: &[u8], t: &[u8], k: i64) -> bool {
    if s.len() != t.len() {
        return false;
    }

    let mut counts: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < 26 {
        counts.push(0);
        i += 1;
    }

    let n = s.len();
    let mut i = 0;
    while i < n {
        let a = s[i] as i64;
        let b = t[i] as i64;
        let mut diff = b - a;
        if diff < 0 {
            diff += 26;
        }

        if diff != 0 {
            let idx = diff as usize;
            let c = counts[idx];
            let needed_move = diff + 26 * c;
            if needed_move > k {
                return false;
            }
            counts[idx] = c + 1;
        }

        i += 1;
    }

    true
}
