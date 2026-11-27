pub fn max_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut max_val: i64 = nums[0];
    let mut sum: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];

        if x > max_val {
            max_val = x;
        }

        if x > 0 {
            let mut seen: bool = false;
            let mut j: usize = 0;
            while j < i {
                if nums[j] == x {
                    seen = true;
                }
                j += 1;
            }

            if !seen {
                sum += x;
            }
        }

        i += 1;
    }

    if sum > 0 {
        sum
    } else {
        max_val
    }
}
