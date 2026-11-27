pub fn is_balanced(num: &[u8]) -> bool {
    let n = num.len();
    let mut even_sum: i64 = 0;
    let mut odd_sum: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let digit: i64 = (num[i] - b'0') as i64;
        if i % 2 == 0 {
            even_sum += digit;
        } else {
            odd_sum += digit;
        }
        i += 1;
    }

    even_sum == odd_sum
}
