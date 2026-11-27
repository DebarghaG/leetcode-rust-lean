pub fn missing_number(arr: &[i64]) -> i64 {
    let n = arr.len();

    let mut sum: i64 = 0;
    let mut i = 0usize;
    while i < n {
        sum += arr[i];
        i += 1;
    }

    // The original array had (n + 1) terms forming an arithmetic progression
    // with the same first and last values as `arr`. Its total sum is
    // (n + 1) * (first + last) / 2. The removed value is the difference.
    let total = (n as i64 + 1) * (arr[0] + arr[n - 1]) / 2;
    total - sum
}
