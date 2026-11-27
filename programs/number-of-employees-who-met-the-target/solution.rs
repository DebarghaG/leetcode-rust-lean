pub fn number_of_employees_who_met_target(hours: &[i64], target: i64) -> i64 {
    let mut count: i64 = 0;
    let n = hours.len();
    let mut i: usize = 0;
    while i < n {
        if hours[i] >= target {
            count += 1;
        }
        i += 1;
    }
    count
}
