pub fn get_final_state(nums: &[i64], k: i64, multiplier: i64) -> Vec<i64> {
    let n = nums.len();
    let mut res: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        res.push(nums[i]);
        i += 1;
    }

    let mut op: i64 = 0;
    while op < k {
        let mut min_idx: usize = 0;
        let mut j: usize = 1;

        while j < n {
            if res[j] < res[min_idx] {
                min_idx = j;
            }
            j += 1;
        }

        res[min_idx] = res[min_idx] * multiplier;
        op += 1;
    }

    res
}
