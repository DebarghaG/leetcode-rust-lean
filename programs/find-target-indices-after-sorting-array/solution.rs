pub fn target_indices(nums: &[i64], target: i64) -> Vec<i64> {
    let mut less: i64 = 0;
    let mut equal: i64 = 0;

    let mut i: usize = 0;
    while i < nums.len() {
        if nums[i] < target {
            less += 1;
        } else if nums[i] == target {
            equal += 1;
        }
        i += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut idx: i64 = less;
    while idx < less + equal {
        result.push(idx);
        idx += 1;
    }

    result
}
