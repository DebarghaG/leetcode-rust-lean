pub fn count_tested_devices(batteryPercentages: &[i64]) -> i64 {
    let n = batteryPercentages.len();
    let mut tested: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if batteryPercentages[i] > tested {
            tested += 1;
        }
        i += 1;
    }

    tested
}
