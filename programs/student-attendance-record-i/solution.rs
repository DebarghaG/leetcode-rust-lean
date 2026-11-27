pub fn check_record(s: &[u8]) -> bool {
    let mut absent: i64 = 0;
    let mut late_streak: i64 = 0;
    let mut i: usize = 0;

    while i < s.len() {
        let c = s[i];
        if c == b'A' {
            absent += 1;
            late_streak = 0;
            if absent >= 2 {
                return false;
            }
        } else if c == b'L' {
            late_streak += 1;
            if late_streak >= 3 {
                return false;
            }
        } else {
            late_streak = 0;
        }
        i += 1;
    }

    true
}
