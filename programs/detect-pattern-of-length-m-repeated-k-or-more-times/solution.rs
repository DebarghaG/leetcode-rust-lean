pub fn contains_pattern(arr: &[i64], m: i64, k: i64) -> bool {
    let n: usize = arr.len();
    let mu: usize = m as usize;
    // Number of consecutive matches of arr[i] == arr[i - m] needed
    // before we have seen the pattern repeated k times.
    let target: i64 = m * (k - 1);

    let mut cnt: i64 = 0;
    let mut i: usize = mu;
    while i < n {
        if arr[i] == arr[i - mu] {
            cnt += 1;
        } else {
            cnt = 0;
        }
        if cnt == target {
            return true;
        }
        i += 1;
    }
    false
}
