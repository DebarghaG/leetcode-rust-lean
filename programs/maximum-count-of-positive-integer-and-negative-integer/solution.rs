pub fn maximum_count(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut neg: i64 = 0;
    let mut pos: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        if nums[i] < 0 {
            neg = neg + 1;
        } else if nums[i] > 0 {
            pos = pos + 1;
        }
        i = i + 1;
    }

    if neg > pos {
        neg
    } else {
        pos
    }
}
