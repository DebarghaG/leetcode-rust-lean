pub fn max_subarrays(nums: &[i64]) -> i64 {
    let mut cur: i64 = -1;
    let mut count: i64 = 0;
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        cur = cur & nums[i];
        if cur == 0 {
            count += 1;
            cur = -1;
        }
        i += 1;
    }

    if count == 0 {
        1
    } else {
        count
    }
}
