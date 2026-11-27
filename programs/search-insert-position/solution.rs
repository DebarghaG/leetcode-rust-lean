pub fn search_insert(nums: &[i64], target: i64) -> i64 {
    let mut lo: usize = 0;
    let mut hi: usize = nums.len();

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if nums[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo as i64
}
