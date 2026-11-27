pub fn h_index(citations: &[i64]) -> i64 {
    let n: usize = citations.len();

    // h-index cannot exceed 1000 because citations[i] <= 1000.
    // Use an exclusive upper bound 1001.
    let mut lo: usize = 0;
    let mut hi: usize = 1001;

    let mut lo64: i64 = 0;
    let mut hi64: i64 = 1001;

    let mut ans: i64 = 0;

    while lo < hi {
        let mid: usize = (lo + hi) / 2;
        let mid64: i64 = (lo64 + hi64) / 2;

        let mut valid: bool = false;

        if mid > n {
            valid = false;
        } else if mid == 0 {
            valid = true;
        } else {
            let idx: usize = n - mid;
            if citations[idx] >= mid64 {
                valid = true;
            }
        }

        if valid {
            ans = mid64;
            lo = mid + 1;
            lo64 = mid64 + 1;
        } else {
            hi = mid;
            hi64 = mid64;
        }
    }

    ans
}
