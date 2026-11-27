pub fn count_substrings(s: &[u8]) -> i64 {
    let n = s.len();
    let mut count: i64 = 0;
    let mut center: usize = 0;

    while center < n {
        // Odd-length palindromes centered at center.
        let mut l = center;
        let mut r = center;
        while r < n && s[l] == s[r] {
            count += 1;
            if l == 0 {
                break;
            }
            l -= 1;
            r += 1;
        }

        // Even-length palindromes centered between center and center + 1.
        let mut l2 = center;
        let mut r2 = center + 1;
        while r2 < n && s[l2] == s[r2] {
            count += 1;
            if l2 == 0 {
                break;
            }
            l2 -= 1;
            r2 += 1;
        }

        center += 1;
    }

    count
}
