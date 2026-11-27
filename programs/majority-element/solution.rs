pub fn majority_element(nums: &[i64]) -> i64 {
    let mut candidate: i64 = 0;
    let mut count: i64 = 0;
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        if count == 0 {
            candidate = nums[i];
            count = 1;
        } else if nums[i] == candidate {
            count = count + 1;
        } else {
            count = count - 1;
        }
        i = i + 1;
    }

    candidate
}
