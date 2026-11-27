pub fn check(nums: &[i64]) -> bool {
    let n = nums.len();
    if n == 0 {
        return true;
    }
    let mut cnt: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let next = (i + 1) % n;
        if nums[i] > nums[next] {
            cnt += 1;
        }
        i += 1;
    }
    cnt <= 1
}
