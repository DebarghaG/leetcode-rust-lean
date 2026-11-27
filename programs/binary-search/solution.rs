pub fn search(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();
    let mut lo: usize = 0;
    let mut hi: usize = n;

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;

        if nums[mid] == target {
            return mid as i64;
        } else if nums[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    -1
}
