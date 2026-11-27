pub fn has_same_digits(s: &[u8]) -> bool {
    let n = s.len();
    let mut cur: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        cur.push((s[i] - b'0') as i64);
        i += 1;
    }

    while cur.len() > 2 {
        let m = cur.len();
        let mut next: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j + 1 < m {
            let v = (cur[j] + cur[j + 1]) % 10;
            next.push(v);
            j += 1;
        }
        cur = next;
    }

    cur[0] == cur[1]
}
