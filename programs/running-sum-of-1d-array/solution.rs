pub fn running_sum(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut out: Vec<i64> = Vec::new();
    let mut acc: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        acc = acc + nums[i];
        out.push(acc);
        i += 1;
    }
    out
}
