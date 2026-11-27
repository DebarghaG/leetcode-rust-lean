pub fn can_divide_into_subsequences(nums: &[i64], k: i64) -> bool {
    let n = nums.len();
    if n == 0 {
        return true;
    }

    // The array can be split as required iff max frequency * k <= n,
    // i.e. every value occurs at most floor(n / k) times.
    let limit: i64 = (n as i64) / k;

    let mut cur_freq: i64 = 1;
    let mut i: usize = 1;
    while i < n {
        if nums[i] == nums[i - 1] {
            cur_freq = cur_freq + 1;
        } else {
            cur_freq = 1;
        }
        if cur_freq > limit {
            return false;
        }
        i = i + 1;
    }

    true
}
