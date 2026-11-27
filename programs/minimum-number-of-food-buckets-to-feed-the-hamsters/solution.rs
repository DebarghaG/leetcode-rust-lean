pub fn minimum_buckets(hamsters: &[u8]) -> i64 {
    let n = hamsters.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if hamsters[i] == b'H' {
            if i + 1 < n && hamsters[i + 1] == b'.' {
                ans += 1;
                i += 3;
            } else if i > 0 && hamsters[i - 1] == b'.' {
                ans += 1;
                i += 1;
            } else {
                return -1;
            }
        } else {
            i += 1;
        }
    }

    ans
}
