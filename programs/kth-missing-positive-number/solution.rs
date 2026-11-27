pub fn find_kth_positive(arr: &[i64], k: i64) -> i64 {
    let n = arr.len();
    if n == 0 {
        return k;
    }

    let mut missing: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let prev: i64 = if i == 0 { 0 } else { arr[i - 1] };
        let gap: i64 = arr[i] - prev - 1;

        if missing + gap >= k {
            return prev + (k - missing);
        }

        missing += gap;
        i += 1;
    }

    arr[n - 1] + (k - missing)
}
