pub fn find_peak_element(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut lo: usize = 0;
    let mut hi: usize = n - 1;

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if nums[mid] < nums[mid + 1] {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo as i64
}
