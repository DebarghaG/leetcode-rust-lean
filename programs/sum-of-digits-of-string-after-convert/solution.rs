pub fn get_lucky(s: &[u8], k: i64) -> i64 {
    let mut sum: i64 = 0;
    let mut i: usize = 0;

    while i < s.len() {
        let val: i64 = (s[i] - b'a') as i64 + 1;
        sum = sum + (val / 10) + (val % 10);
        i = i + 1;
    }

    let mut step: i64 = 1;
    while step < k {
        let mut x: i64 = sum;
        let mut digit_sum: i64 = 0;

        while x > 0 {
            digit_sum = digit_sum + (x % 10);
            x = x / 10;
        }

        sum = digit_sum;
        step = step + 1;
    }

    sum
}
