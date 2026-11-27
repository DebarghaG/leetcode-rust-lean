pub fn count_k_constraint_substrings(s: &[u8], k: i64) -> i64 {
    let n = s.len();
    let mut ans: i64 = 0;

    let mut left: usize = 0;
    while left < n {
        let mut zeros: i64 = 0;
        let mut ones: i64 = 0;
        let mut right: usize = left;

        while right < n {
            if s[right] == b'0' {
                zeros += 1;
            } else {
                ones += 1;
            }

            if zeros <= k || ones <= k {
                ans += 1;
            }

            right += 1;
        }

        left += 1;
    }

    ans
}
