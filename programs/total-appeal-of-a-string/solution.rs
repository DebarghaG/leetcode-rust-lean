pub fn appeal_sum(s: &[u8]) -> i64 {
    let n = s.len();

    let mut last: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        last.push(-1);
        k += 1;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let idx: usize = s[i] as usize - 97;
        let prev: i64 = last[idx];

        let left: i64 = i as i64 - prev;
        let right: i64 = n as i64 - i as i64;

        total += left * right;
        last[idx] = i as i64;

        i += 1;
    }

    total
}
