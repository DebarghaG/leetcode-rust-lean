pub fn second_highest(s: &[u8]) -> i64 {
    let mut largest: i64 = -1;
    let mut second: i64 = -1;

    let mut i: usize = 0;
    while i < s.len() {
        let b = s[i];
        if b >= b'0' && b <= b'9' {
            let d: i64 = (b - b'0') as i64;

            if d > largest {
                second = largest;
                largest = d;
            } else if d < largest && d > second {
                second = d;
            }
        }
        i += 1;
    }

    second
}
