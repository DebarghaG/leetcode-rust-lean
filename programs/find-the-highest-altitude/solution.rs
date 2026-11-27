pub fn largest_altitude(gain: &[i64]) -> i64 {
    let n = gain.len();
    let mut altitude: i64 = 0;
    let mut best: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        altitude = altitude + gain[i];
        if altitude > best {
            best = altitude;
        }
        i = i + 1;
    }
    best
}
