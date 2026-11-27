pub fn minimum_time(s: &[u8]) -> i64 {
    let len: usize = s.len();

    let mut n: i64 = 0;
    let mut k: usize = 0;
    while k < len {
        n = n + 1;
        k = k + 1;
    }

    let mut ans: i64 = n;
    let mut prefix_ones: i64 = 0;
    let mut min_left: i64 = 0;

    let mut i: usize = 0;
    let mut b: i64 = 0;

    while i < len {
        if s[i] == b'1' {
            prefix_ones = prefix_ones + 1;
        }

        b = b + 1;

        let left_term: i64 = b - 2 * prefix_ones;
        if left_term < min_left {
            min_left = left_term;
        }

        let right_term: i64 = 2 * prefix_ones - b;
        let candidate: i64 = n + min_left + right_term;
        if candidate < ans {
            ans = candidate;
        }

        i = i + 1;
    }

    ans
}
