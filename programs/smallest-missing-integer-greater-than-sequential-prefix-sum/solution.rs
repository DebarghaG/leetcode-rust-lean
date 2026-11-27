fn contains(nums: &[i64], x: i64) -> bool {
    let mut i: usize = 0;
    while i < nums.len() {
        if nums[i] == x {
            return true;
        }
        i += 1;
    }
    false
}

pub fn missing_integer(nums: &[i64]) -> i64 {
    if nums.len() == 0 {
        return 1;
    }

    let mut sum: i64 = nums[0];
    let mut i: usize = 1;

    while i < nums.len() {
        if nums[i] == nums[i - 1] + 1 {
            sum += nums[i];
            i += 1;
        } else {
            break;
        }
    }

    let mut x: i64 = sum;
    while contains(nums, x) {
        x += 1;
    }

    x
}
