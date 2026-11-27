pub fn seconds_to_remove_occurrences(s: &[u8]) -> i64 {
    let n = s.len();
    let mut zeros: i64 = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'0' {
            zeros += 1;
        } else {
            if zeros > 0 {
                let next = ans + 1;
                if zeros > next {
                    ans = zeros;
                } else {
                    ans = next;
                }
            }
        }
        i += 1;
    }

    ans
}
