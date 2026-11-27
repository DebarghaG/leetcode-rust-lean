pub fn get_min_distance(nums: &[i64], target: i64, start: i64) -> i64 {
    let n = nums.len();
    let mut ans = n as i64;
    let mut i = 0;
    while i < n {
        if nums[i] == target {
            let idx = i as i64;
            let d = if idx >= start { idx - start } else { start - idx };
            if d < ans {
                ans = d;
            }
        }
        i += 1;
    }
    ans
}
