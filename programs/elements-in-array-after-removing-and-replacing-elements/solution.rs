pub fn element_in_nums(nums: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n_usize = nums.len();
    let n = n_usize as i64;
    let period = n + n;

    let mut ans: Vec<i64> = Vec::new();
    let mut qi: usize = 0;

    while qi < queries.len() {
        let q = &queries[qi];
        let t = q[0];
        let index = q[1];

        let r = t % period;
        let mut value: i64 = -1;

        if r < n {
            let pos = r + index;
            if pos < n {
                value = nums[pos as usize];
            }
        } else {
            let filled = r - n;
            if index < filled {
                value = nums[index as usize];
            }
        }

        ans.push(value);
        qi += 1;
    }

    ans
}
