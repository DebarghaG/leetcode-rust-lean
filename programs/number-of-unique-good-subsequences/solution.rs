pub fn number_of_unique_good_subsequences(binary: &[u8]) -> i64 {
    let modv: i64 = 1000000007;
    let mut dp0: i64 = 0;
    let mut dp1: i64 = 0;
    let mut has_zero: bool = false;

    let n = binary.len();
    let mut i: usize = 0;

    while i < n {
        if binary[i] == b'0' {
            dp0 = (dp0 + dp1) % modv;
            has_zero = true;
        } else {
            dp1 = (dp0 + dp1 + 1) % modv;
        }
        i += 1;
    }

    let mut ans = (dp0 + dp1) % modv;
    if has_zero {
        ans = (ans + 1) % modv;
    }

    ans
}
