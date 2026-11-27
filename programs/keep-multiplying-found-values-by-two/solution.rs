pub fn find_final_value(nums: &[i64], original: i64) -> i64 {
    let mut current: i64 = original;

    loop {
        let mut found: bool = false;
        let mut i: usize = 0;

        while i < nums.len() {
            if nums[i] == current {
                found = true;
            }
            i += 1;
        }

        if found {
            current = current * 2;
        } else {
            return current;
        }
    }
}
