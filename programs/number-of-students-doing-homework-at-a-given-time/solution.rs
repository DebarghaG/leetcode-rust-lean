pub fn busy_student(startTime: &[i64], endTime: &[i64], queryTime: i64) -> i64 {
    let n = startTime.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if startTime[i] <= queryTime && queryTime <= endTime[i] {
            count += 1;
        }
        i += 1;
    }
    count
}
