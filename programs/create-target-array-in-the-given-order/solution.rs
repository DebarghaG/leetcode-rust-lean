pub fn create_target_array(nums: &[i64], index: &[i64]) -> Vec<i64> {
    let mut target: Vec<i64> = Vec::new();
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let mut pos = index[i] as usize;
        if pos > i {
            pos = i;
        }

        let value = nums[i];
        target.push(value);

        let mut j = i;
        while j > pos {
            target[j] = target[j - 1];
            j -= 1;
        }
        target[pos] = value;

        i += 1;
    }

    target
}
