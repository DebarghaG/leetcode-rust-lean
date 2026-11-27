pub fn find_prefix_score(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut ans: Vec<i64> = Vec::new();
    let mut cur_max: i64 = 0;
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let v = nums[i];
        if i == 0 || v > cur_max {
            cur_max = v;
        }
        sum = sum + v + cur_max;
        ans.push(sum);
        i += 1;
    }
    ans
}
