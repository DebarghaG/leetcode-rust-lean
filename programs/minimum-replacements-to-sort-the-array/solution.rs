pub fn minimum_replacement(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    let mut operations: i64 = 0;
    let mut prev: i64 = nums[n - 1];
    let mut i: usize = n - 1;

    while i > 0 {
        i -= 1;
        let value = nums[i];

        if value <= prev {
            prev = value;
        } else {
            let parts = (value + prev - 1) / prev;
            operations += parts - 1;
            prev = value / parts;
        }
    }

    operations
}
