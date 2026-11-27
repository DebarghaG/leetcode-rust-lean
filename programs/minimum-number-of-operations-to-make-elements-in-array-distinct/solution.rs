pub fn minimum_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut ops: i64 = 0;
    let mut start: usize = 0;
    let mut done: bool = false;

    while !done {
        // Check whether nums[start..] contains all distinct elements.
        let mut distinct: bool = true;
        let mut i: usize = start;
        while i < n {
            let mut j: usize = i + 1;
            while j < n {
                if nums[i] == nums[j] {
                    distinct = false;
                }
                j = j + 1;
            }
            i = i + 1;
        }

        if distinct {
            done = true;
        } else {
            start = start + 3;
            ops = ops + 1;
            if start >= n {
                done = true;
            }
        }
    }

    ops
}
