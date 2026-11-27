pub fn or_array(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut out: Vec<i64> = Vec::new();
    if n < 2 {
        return out;
    }
    let mut i: usize = 0;
    while i + 1 < n {
        out.push(nums[i] | nums[i + 1]);
        i += 1;
    }
    out
}
