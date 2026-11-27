pub fn check_possibility(nums: &[i64]) -> bool {
    let n = nums.len();
    let mut count: i64 = 0;
    let mut bad: usize = 0;
    let mut prev: i64 = 0;

    if n > 0 {
        prev = nums[0];
    }

    for i in 0..n {
        let cur: i64 = nums[i];
        if i > 0 {
            if prev > cur {
                count = count + 1;
                bad = i - 1;
            }
        }
        prev = cur;
    }

    if count > 1 {
        return false;
    }
    if count == 0 {
        return true;
    }
    if bad == 0 {
        return true;
    }
    if bad + 2 == n {
        return true;
    }
    if nums[bad - 1] <= nums[bad + 1] {
        return true;
    }
    if nums[bad] <= nums[bad + 2] {
        return true;
    }
    false
}
