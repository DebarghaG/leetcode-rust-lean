pub fn have_conflict(event1: &[Vec<u8>], event2: &[Vec<u8>]) -> bool {
    let s1_hour: i64 =
        ((event1[0][0] as i64) - 48) * 10 + ((event1[0][1] as i64) - 48);
    let s1_minute: i64 =
        ((event1[0][3] as i64) - 48) * 10 + ((event1[0][4] as i64) - 48);

    let e1_hour: i64 =
        ((event1[1][0] as i64) - 48) * 10 + ((event1[1][1] as i64) - 48);
    let e1_minute: i64 =
        ((event1[1][3] as i64) - 48) * 10 + ((event1[1][4] as i64) - 48);

    let s2_hour: i64 =
        ((event2[0][0] as i64) - 48) * 10 + ((event2[0][1] as i64) - 48);
    let s2_minute: i64 =
        ((event2[0][3] as i64) - 48) * 10 + ((event2[0][4] as i64) - 48);

    let e2_hour: i64 =
        ((event2[1][0] as i64) - 48) * 10 + ((event2[1][1] as i64) - 48);
    let e2_minute: i64 =
        ((event2[1][3] as i64) - 48) * 10 + ((event2[1][4] as i64) - 48);

    let start1: i64 = s1_hour * 60 + s1_minute;
    let end1: i64 = e1_hour * 60 + e1_minute;
    let start2: i64 = s2_hour * 60 + s2_minute;
    let end2: i64 = e2_hour * 60 + e2_minute;

    start1 <= end2 && start2 <= end1
}
