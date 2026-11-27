fn parse_minutes(t: &[u8]) -> i64 {
    let h0: i64 = t[0] as i64 - 48;
    let h1: i64 = t[1] as i64 - 48;
    let m0: i64 = t[3] as i64 - 48;
    let m1: i64 = t[4] as i64 - 48;

    let hh: i64 = h0 * 10 + h1;
    let mm: i64 = m0 * 10 + m1;

    hh * 60 + mm
}

pub fn number_of_rounds(loginTime: &[u8], logoutTime: &[u8]) -> i64 {
    let login: i64 = parse_minutes(loginTime);
    let mut logout: i64 = parse_minutes(logoutTime);

    if logout < login {
        logout += 24 * 60;
    }

    let first_round: i64 = (login + 14) / 15;
    let last_round: i64 = logout / 15;

    let ans: i64 = last_round - first_round;

    if ans > 0 {
        ans
    } else {
        0
    }
}
