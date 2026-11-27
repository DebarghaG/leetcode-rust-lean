pub fn count_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut ans: i64 = 1;
    let mut run: i64 = 1;
    let mut i: usize = 1;

    while i < n {
        if nums[i] > nums[i - 1] {
            run += 1;
        } else {
            run = 1;
        }
        ans += run;
        i += 1;
    }

    ans
}
