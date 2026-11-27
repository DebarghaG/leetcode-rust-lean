pub fn count_time(time: &[u8]) -> i64 {
    let mut ans: i64 = 0;
    let mut h: i64 = 0;

    while h < 24 {
        let h0: i64 = h / 10;
        let h1: i64 = h % 10;

        let mut m: i64 = 0;
        while m < 60 {
            let m0: i64 = m / 10;
            let m1: i64 = m % 10;

            if digit_ok(time[0], h0)
                && digit_ok(time[1], h1)
                && digit_ok(time[3], m0)
                && digit_ok(time[4], m1)
            {
                ans += 1;
            }

            m += 1;
        }

        h += 1;
    }

    ans
}

fn digit_ok(c: u8, d: i64) -> bool {
    if c == b'?' {
        true
    } else {
        c as i64 == 48 + d
    }
}
