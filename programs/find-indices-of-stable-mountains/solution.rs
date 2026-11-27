pub fn stable_mountains(height: &[i64], threshold: i64) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let n = height.len();
    let mut i: usize = 1;

    while i < n {
        if height[i - 1] > threshold {
            out.push(i as i64);
        }
        i += 1;
    }

    out
}
