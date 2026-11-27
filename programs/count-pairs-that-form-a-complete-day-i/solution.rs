pub fn count_complete_day_pairs(hours: &[i64]) -> i64 {
    let n = hours.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = i + 1;
        while j < n {
            if (hours[i] % 24 + hours[j] % 24) % 24 == 0 {
                count += 1;
            }
            j += 1;
        }
        i += 1;
    }
    count
}
