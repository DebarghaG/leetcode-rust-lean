pub fn digit_count(num: &[u8]) -> bool {
    let n = num.len();
    let mut i: usize = 0;
    while i < n {
        let target = b'0' + (i as u8);
        let mut count: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            if num[j] == target {
                count += 1;
            }
            j += 1;
        }
        let expected = (num[i] - b'0') as i64;
        if count != expected {
            return false;
        }
        i += 1;
    }
    true
}
