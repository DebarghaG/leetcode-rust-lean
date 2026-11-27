pub fn is_substring_present(s: &[u8]) -> bool {
    let n = s.len();
    let mut found = false;
    if n >= 2 {
        let mut i: usize = 0;
        while i + 1 < n && !found {
            let mut j: usize = 0;
            while j + 1 < n {
                if s[i] == s[j + 1] && s[i + 1] == s[j] {
                    found = true;
                    break;
                }
                j += 1;
            }
            i += 1;
        }
    }
    found
}
