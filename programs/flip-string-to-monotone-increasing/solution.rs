pub fn min_flips_mono_incr(s: &[u8]) -> i64 {
    let n = s.len();

    let mut zeros: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if s[i] == b'0' {
            zeros += 1;
        }
        i += 1;
    }

    let mut ones: i64 = 0;
    let mut ans: i64 = zeros;
    i = 0;
    while i < n {
        if s[i] == b'1' {
            ones += 1;
        } else {
            zeros -= 1;
        }

        let cost: i64 = ones + zeros;
        if cost < ans {
            ans = cost;
        }

        i += 1;
    }

    ans
}
