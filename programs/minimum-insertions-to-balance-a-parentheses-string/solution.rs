pub fn min_insertions(s: &[u8]) -> i64 {
    let n = s.len();
    let mut ans: i64 = 0;
    let mut need: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if s[i] == b'(' {
            need += 2;
            if need % 2 == 1 {
                ans += 1;
                need -= 1;
            }
        } else {
            need -= 1;
            if need < 0 {
                ans += 1;
                need = 1;
            }
        }
        i += 1;
    }

    ans + need
}
