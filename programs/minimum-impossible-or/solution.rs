pub fn min_impossible_or(nums: &[i64]) -> i64 {
    let mut p: i64 = 1;
    let mut checked: usize = 0;

    while checked < 32 {
        let mut found: bool = false;
        let mut i: usize = 0;

        while i < nums.len() {
            if nums[i] == p {
                found = true;
            }
            i += 1;
        }

        if !found {
            return p;
        }

        p *= 2;
        checked += 1;
    }

    p
}
