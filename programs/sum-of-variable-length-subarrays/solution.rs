pub fn subarray_sum(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut start: usize = i;
        let mut remaining: i64 = nums[i];

        while remaining > 0 && start > 0 {
            start = start - 1;
            remaining = remaining - 1;
        }

        let mut sum: i64 = 0;
        let mut j: usize = start;

        while j <= i {
            sum = sum + nums[j];
            j = j + 1;
        }

        total = total + sum;
        i = i + 1;
    }

    total
}
