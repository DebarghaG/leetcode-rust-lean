pub fn find_the_longest_balanced_substring(s: &[u8]) -> i64 {
    let n = s.len();
    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'0' {
            let mut zeros: i64 = 0;
            while i < n && s[i] == b'0' {
                zeros += 1;
                i += 1;
            }

            let mut ones: i64 = 0;
            while i < n && s[i] == b'1' {
                ones += 1;
                i += 1;
            }

            let m = if zeros < ones { zeros } else { ones };
            let len = 2 * m;
            if len > best {
                best = len;
            }
        } else {
            i += 1;
        }
    }

    best
}
