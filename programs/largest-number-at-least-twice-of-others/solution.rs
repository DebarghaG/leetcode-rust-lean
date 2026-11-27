pub fn dominant_index(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut max_val = nums[0];
    let mut max_idx: usize = 0;

    let mut i: usize = 1;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
            max_idx = i;
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < n {
        if j != max_idx {
            if nums[j] * 2 > max_val {
                return -1;
            }
        }
        j += 1;
    }

    max_idx as i64
}
