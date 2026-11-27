pub fn prefixes_div_by5(nums: &[i64]) -> Vec<bool> {
    let mut answer: Vec<bool> = Vec::new();
    let mut rem: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        rem = (rem * 2 + nums[i]) % 5;
        answer.push(rem == 0);
        i += 1;
    }

    answer
}
