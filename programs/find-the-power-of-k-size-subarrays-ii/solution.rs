pub fn results_array(nums: &[i64], k: i64) -> Vec<i64> {
    let n = nums.len();
    let k_usize = k as usize;
    let mut result: Vec<i64> = Vec::new();

    let mut run: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if i == 0 {
            run = 1;
        } else {
            if nums[i] == nums[i - 1] + 1 {
                run = run + 1;
            } else {
                run = 1;
            }
        }

        if i + 1 >= k_usize {
            if run >= k {
                result.push(nums[i]);
            } else {
                result.push(-1);
            }
        }

        i = i + 1;
    }

    result
}
