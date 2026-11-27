pub fn number_of_special_substrings(s: &[u8]) -> i64 {
    let mut last: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        last.push(-1);
        k += 1;
    }

    let n: usize = s.len();
    let mut left: i64 = 0;
    let mut total: i64 = 0;
    let mut r: usize = 0;

    while r < n {
        let c: usize = (s[r] - b'a') as usize;

        if last[c] >= left {
            left = last[c] + 1;
        }

        last[c] = r as i64;
        total += (r as i64) - left + 1;

        r += 1;
    }

    total
}
