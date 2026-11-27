pub fn number_of_substrings(s: &[u8], k: i64) -> i64 {
    let n = s.len();

    let mut freq: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        freq.push(0);
        i += 1;
    }

    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut total: i64 = 0;

    while right < n {
        let ci: usize = (s[right] - b'a') as usize;
        freq[ci] += 1;

        while freq[ci] >= k {
            let li: usize = (s[left] - b'a') as usize;
            freq[li] -= 1;
            left += 1;
        }

        total += left as i64;
        right += 1;
    }

    total
}
