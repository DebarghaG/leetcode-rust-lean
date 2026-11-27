pub fn sum_game(num: &[u8]) -> bool {
    let n = num.len();
    let half = n / 2;

    let mut sum1: i64 = 0;
    let mut sum2: i64 = 0;
    let mut q1: i64 = 0;
    let mut q2: i64 = 0;

    let mut i: usize = 0;
    while i < half {
        let c = num[i];
        if c == b'?' {
            q1 += 1;
        } else {
            sum1 += (c - b'0') as i64;
        }
        i += 1;
    }

    i = half;
    while i < n {
        let c = num[i];
        if c == b'?' {
            q2 += 1;
        } else {
            sum2 += (c - b'0') as i64;
        }
        i += 1;
    }

    let left = 2 * (sum1 - sum2);
    let right = 9 * (q2 - q1);

    left != right
}
