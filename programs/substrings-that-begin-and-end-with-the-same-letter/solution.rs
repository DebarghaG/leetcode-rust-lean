pub fn number_of_substrings(s: &[u8]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < 26 {
        counts.push(0);
        j += 1;
    }

    let mut ans: i64 = 0;
    let mut i: usize = 0;
    let n: usize = s.len();

    while i < n {
        let idx: usize = (s[i] - b'a') as usize;
        ans = ans + counts[idx] + 1;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    ans
}
