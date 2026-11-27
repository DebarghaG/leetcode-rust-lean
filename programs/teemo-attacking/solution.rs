pub fn find_poisoned_duration(timeSeries: &[i64], duration: i64) -> i64 {
    let n = timeSeries.len();
    if n == 0 {
        return 0;
    }

    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        let gap = timeSeries[i + 1] - timeSeries[i];
        if gap < duration {
            total += gap;
        } else {
            total += duration;
        }
        i += 1;
    }

    total += duration;
    total
}
