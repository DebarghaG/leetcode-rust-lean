pub fn find_peaks(mountain: &[i64]) -> Vec<i64> {
    let mut peaks: Vec<i64> = Vec::new();
    let n = mountain.len();

    if n < 3 {
        return peaks;
    }

    let mut i: usize = 1;
    while i + 1 < n {
        if mountain[i] > mountain[i - 1] && mountain[i] > mountain[i + 1] {
            peaks.push(i as i64);
        }
        i += 1;
    }

    peaks
}
