pub fn minimum_array_length(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut mn = nums[0];
    let mut i = 0;
    while i < n {
        if nums[i] < mn {
            mn = nums[i];
        }
        i += 1;
    }

    let mut count_min: i64 = 0;
    let mut all_divisible = true;

    i = 0;
    while i < n {
        let x = nums[i];
        if x == mn {
            count_min += 1;
        }
        if x % mn != 0 {
            all_divisible = false;
        }
        i += 1;
    }

    if !all_divisible {
        return 1;
    }

    (count_min + 1) / 2
}
