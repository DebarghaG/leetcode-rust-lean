pub fn number_of_substrings(s: &[u8], k: i64) -> i64 {
    let n: usize = s.len();
    let mut ans: i64 = 0;
    let mut left: usize = 0;

    while left < n {
        let mut cnt: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < 26 {
            cnt.push(0);
            i += 1;
        }

        let mut right: usize = left;
        while right < n {
            let idx: usize = (s[right] - b'a') as usize;
            cnt[idx] = cnt[idx] + 1;

            if cnt[idx] >= k {
                ans = ans + (n - right) as i64;
                right = n;
            } else {
                right += 1;
            }
        }

        left += 1;
    }

    ans
}
