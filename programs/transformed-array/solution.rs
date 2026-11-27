pub fn construct_transformed_array(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let n_i64 = n as i64;
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        let mut idx: i64 = (i as i64) + nums[i];
        idx = idx % n_i64;
        if idx < 0 {
            idx = idx + n_i64;
        }

        let target = idx as usize;
        result.push(nums[target]);
        i += 1;
    }

    result
}
