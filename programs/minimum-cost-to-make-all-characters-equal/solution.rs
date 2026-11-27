pub fn minimum_cost(s: &[u8]) -> i64 {
    let n: usize = s.len();
    let mut ans: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        if s[i] != s[i - 1] {
            let left: i64 = i as i64;
            let right: i64 = (n - i) as i64;
            if left < right {
                ans += left;
            } else {
                ans += right;
            }
        }
        i += 1;
    }

    ans
}
