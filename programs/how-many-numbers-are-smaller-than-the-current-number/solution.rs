pub fn smaller_numbers_than_current(nums: &[i64]) -> Vec<i64> {
    let mut ans: Vec<i64> = Vec::new();
    let n = nums.len();
    let mut i: usize = 0;

    while i < n {
        let mut count: i64 = 0;
        let mut j: usize = 0;

        while j < n {
            if nums[j] < nums[i] {
                count += 1;
            }
            j += 1;
        }

        ans.push(count);
        i += 1;
    }

    ans
}
