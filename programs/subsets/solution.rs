pub fn subsets(nums: &[i64]) -> Vec<Vec<i64>> {
    let n = nums.len();
    let mut res: Vec<Vec<i64>> = Vec::new();
    res.push(Vec::new());

    let mut processed: usize = 0;
    while processed < n {
        let idx: usize = n - 1 - processed;
        let num: i64 = nums[idx];
        let current_len: usize = res.len();

        let mut j: usize = 0;
        while j < current_len {
            let mut subset: Vec<i64> = Vec::new();
            subset.push(num);

            let existing_len: usize = res[j].len();
            let mut k: usize = 0;
            while k < existing_len {
                subset.push(res[j][k]);
                k += 1;
            }

            res.push(subset);
            j += 1;
        }

        processed += 1;
    }

    res
}
