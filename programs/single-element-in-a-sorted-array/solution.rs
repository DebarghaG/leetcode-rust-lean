pub fn single_non_duplicate(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return nums[0];
    }

    let mut lo: usize = 0;
    let mut hi: usize = n - 1;

    while lo < hi {
        let mut mid: usize = lo + (hi - lo) / 2;
        if mid % 2 == 1 {
            mid -= 1;
        }

        if nums[mid] == nums[mid + 1] {
            lo = mid + 2;
        } else {
            hi = mid;
        }
    }

    nums[lo]
}
