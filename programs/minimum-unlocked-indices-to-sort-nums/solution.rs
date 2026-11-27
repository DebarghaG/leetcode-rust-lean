pub fn min_unlocked_indices(nums: &[i64], locked: &[i64]) -> i64 {
    let n = nums.len();
    if n <= 1 {
        return 0;
    }

    // A value 3 can never move left past a value 1, because only swaps
    // of the form (2,1) and (3,2) are allowed. Therefore every 1 must
    // already appear before every 3.
    let mut seen_three = false;
    let mut i = 0usize;
    while i < n {
        if nums[i] == 3 {
            seen_three = true;
        }
        if nums[i] == 1 && seen_three {
            return -1;
        }
        i += 1;
    }

    let mut total_one = 0usize;
    let mut total_two = 0usize;
    i = 0;
    while i < n {
        if nums[i] == 1 {
            total_one += 1;
        } else if nums[i] == 2 {
            total_two += 1;
        }
        i += 1;
    }

    let mut pref_one = 0usize;
    let mut pref_three = 0usize;
    let mut ans: i64 = 0;

    i = 0;
    while i + 1 < n {
        if nums[i] == 1 {
            pref_one += 1;
        } else if nums[i] == 3 {
            pref_three += 1;
        }

        let len_pref = i + 1;

        // In the fully sorted array, the prefix of length len_pref contains:
        // final_one ones, then final_two twos, then final_three threes.
        let final_one = if len_pref < total_one {
            len_pref
        } else {
            total_one
        };

        let mut final_two = 0usize;
        if len_pref > total_one {
            let rem = len_pref - total_one;
            if rem < total_two {
                final_two = rem;
            } else {
                final_two = total_two;
            }
        }

        let final_three = len_pref - final_one - final_two;

        // A swap across boundary i is necessary if a 1 must enter this
        // prefix, or if a 3 must leave this prefix.
        let need_one = final_one > pref_one;
        let need_three = pref_three > final_three;

        if need_one || need_three {
            if locked[i] == 1 {
                ans += 1;
            }
        }

        i += 1;
    }

    ans
}
