pub fn count_homogenous(s: &[u8]) -> i64 {
    let modv: i64 = 1000000007;
    let n: usize = s.len();
    let mut ans: i64 = 0;
    let mut cur: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        if i == 0 {
            cur = 1;
        } else if s[i] == s[i - 1] {
            cur = cur + 1;
        } else {
            cur = 1;
        }

        ans = (ans + cur) % modv;
        i = i + 1;
    }

    ans
}
