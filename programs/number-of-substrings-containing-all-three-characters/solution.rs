pub fn number_of_substrings(s: &[u8]) -> i64 {
    let n = s.len();
    let mut left: usize = 0;
    let mut count_a: usize = 0;
    let mut count_b: usize = 0;
    let mut count_c: usize = 0;
    let mut total: i64 = 0;
    let mut right: usize = 0;

    while right < n {
        let ch = s[right];
        if ch == b'a' {
            count_a += 1;
        } else if ch == b'b' {
            count_b += 1;
        } else {
            count_c += 1;
        }

        while count_a > 0 && count_b > 0 && count_c > 0 {
            let left_ch = s[left];
            if left_ch == b'a' {
                count_a -= 1;
            } else if left_ch == b'b' {
                count_b -= 1;
            } else {
                count_c -= 1;
            }
            left += 1;
        }

        total += left as i64;
        right += 1;
    }

    total
}
