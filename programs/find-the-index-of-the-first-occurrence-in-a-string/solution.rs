pub fn str_str(haystack: &[u8], needle: &[u8]) -> i64 {
    let n = haystack.len();
    let m = needle.len();

    if m == 0 {
        return 0;
    }
    if m > n {
        return -1;
    }

    let mut i: usize = 0;
    while i + m <= n {
        let mut j: usize = 0;
        let mut matched: bool = true;

        while j < m {
            if haystack[i + j] != needle[j] {
                matched = false;
                break;
            }
            j += 1;
        }

        if matched {
            return i as i64;
        }

        i += 1;
    }

    -1
}
