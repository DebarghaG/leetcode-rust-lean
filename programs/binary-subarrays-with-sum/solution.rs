pub fn num_subarrays_with_sum(nums: &[i64], goal: i64) -> i64 {
    let n = nums.len();

    let mut counts: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i <= n {
        counts.push(0);
        i += 1;
    }

    counts[0] = 1;

    let target = goal as usize;
    let mut prefix = 0usize;
    let mut ans = 0i64;
    let mut j = 0usize;

    while j < n {
        if nums[j] == 1 {
            prefix += 1;
        }

        if prefix >= target {
            ans += counts[prefix - target];
        }

        counts[prefix] += 1;
        j += 1;
    }

    ans
}
