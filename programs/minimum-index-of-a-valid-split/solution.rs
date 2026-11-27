pub fn minimum_index(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return -1;
    }

    // Find the dominant element using Boyer-Moore majority vote.
    let mut candidate = nums[0];
    let mut balance: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if balance == 0 {
            candidate = nums[i];
            balance = 1;
        } else if nums[i] == candidate {
            balance += 1;
        } else {
            balance -= 1;
        }
        i += 1;
    }

    // Count total occurrences of the dominant element.
    let mut total: i64 = 0;
    i = 0;
    while i < n {
        if nums[i] == candidate {
            total += 1;
        }
        i += 1;
    }

    // Try every possible split from left to right.
    let mut left: i64 = 0;
    i = 0;
    while i + 1 < n {
        if nums[i] == candidate {
            left += 1;
        }

        let prefix_len = (i as i64) + 1;
        let suffix_len = (n as i64) - (i as i64) - 1;
        let right = total - left;

        if left * 2 > prefix_len && right * 2 > suffix_len {
            return i as i64;
        }

        i += 1;
    }

    -1
}
