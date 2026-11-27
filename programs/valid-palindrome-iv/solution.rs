pub fn make_palindrome(s: &[u8]) -> bool {
    let n = s.len();
    let mut mismatches: i64 = 0;
    let mut i: usize = 0;

    while i < n / 2 {
        if s[i] != s[n - 1 - i] {
            mismatches += 1;
        }
        i += 1;
    }

    mismatches <= 2
}
