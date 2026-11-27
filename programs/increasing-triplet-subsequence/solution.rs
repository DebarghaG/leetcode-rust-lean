pub fn increasing_triplet(nums: &[i64]) -> bool {
    let mut first: i64 = i64::MAX;
    let mut second: i64 = i64::MAX;

    let mut i: usize = 0;
    while i < nums.len() {
        let x = nums[i];

        if x > second {
            return true;
        } else if x > first {
            second = x;
        } else {
            first = x;
        }

        i += 1;
    }

    false
}
