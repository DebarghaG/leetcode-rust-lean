pub fn alternating_subarray(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut best: i64 = -1;

    if n < 2 {
        return -1;
    }

    let mut i: usize = 0;
    while i + 1 < n {
        if nums[i + 1] == nums[i] + 1 {
            let mut length: i64 = 2;
            let mut expected: i64 = -1;
            let mut j: usize = i + 2;

            while j < n {
                if nums[j] - nums[j - 1] == expected {
                    length = length + 1;
                    expected = -expected;
                    j = j + 1;
                } else {
                    break;
                }
            }

            if length > best {
                best = length;
            }
        }

        i = i + 1;
    }

    best
}
