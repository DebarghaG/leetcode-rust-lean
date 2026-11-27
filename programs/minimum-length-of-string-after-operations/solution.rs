pub fn minimum_length(s: &[u8]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 26 {
        counts.push(0);
        k += 1;
    }

    let n: usize = s.len();
    let mut i: usize = 0;
    while i < n {
        let idx: usize = (s[i] - b'a') as usize;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut j: usize = 0;
    while j < 26 {
        let c: i64 = counts[j];
        if c >= 3 {
            if c % 2 == 0 {
                ans = ans + 2;
            } else {
                ans = ans + 1;
            }
        } else {
            ans = ans + c;
        }
        j += 1;
    }

    ans
}
