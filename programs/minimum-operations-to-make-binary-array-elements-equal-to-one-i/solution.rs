pub fn min_operations(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let mut operations: i64 = 0;
    i = 0;
    while i + 2 < n {
        if a[i] == 0 {
            operations += 1;
            a[i] = 1 - a[i];
            a[i + 1] = 1 - a[i + 1];
            a[i + 2] = 1 - a[i + 2];
        }
        i += 1;
    }

    i = 0;
    while i < n {
        if a[i] != 1 {
            return -1;
        }
        i += 1;
    }

    operations
}
