pub fn can_be_increasing(nums: &[i64]) -> bool {
    let n = nums.len();

    // An array of length 0 or 1 is trivially strictly increasing.
    if n <= 1 {
        return true;
    }

    let mut i: usize = 1;
    let mut prev: i64 = nums[0];
    let mut used: bool = false; // whether we already "removed" one element

    while i < n {
        let cur: i64 = nums[i];

        if prev < cur {
            // Still increasing: advance the effective previous value.
            prev = cur;
        } else {
            // Violation: we must remove exactly one element here.
            if used {
                // A second violation means one removal is not enough.
                return false;
            }
            used = true;

            // Decide which element to drop.
            // remove_prev == true  -> drop nums[i-1] (so prev becomes cur)
            // remove_prev == false -> drop nums[i]   (keep prev unchanged)
            let mut remove_prev: bool = true;
            if i >= 2 {
                if nums[i - 2] >= cur {
                    remove_prev = false;
                }
            }

            if remove_prev {
                prev = cur;
            }
        }

        i = i + 1;
    }

    true
}
