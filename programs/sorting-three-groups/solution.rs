fn min_i64(a: i64, b: i64) -> i64 {
    if a < b {
        a
    } else {
        b
    }
}

pub fn minimum_operations(nums: &[i64]) -> i64 {
    let inf: i64 = 1000000;

    // c0: minimum deletions when keeping no elements so far
    // c1: minimum deletions when the largest kept value is 1
    // c2: minimum deletions when the largest kept value is 2
    // c3: minimum deletions when the largest kept value is 3
    let mut c0: i64 = 0;
    let mut c1: i64 = inf;
    let mut c2: i64 = inf;
    let mut c3: i64 = inf;

    let n: usize = nums.len();
    let mut i: usize = 0;

    while i < n {
        let x: i64 = nums[i];

        // Delete nums[i] from each state.
        let mut n0: i64 = c0 + 1;
        let mut n1: i64 = c1 + 1;
        let mut n2: i64 = c2 + 1;
        let mut n3: i64 = c3 + 1;

        // Keep nums[i] if it can extend the current non-decreasing prefix.
        if x == 1 {
            let best = min_i64(c0, c1);
            n1 = min_i64(n1, best);
        } else if x == 2 {
            let best = min_i64(min_i64(c0, c1), c2);
            n2 = min_i64(n2, best);
        } else {
            let best = min_i64(min_i64(c0, c1), min_i64(c2, c3));
            n3 = min_i64(n3, best);
        }

        c0 = n0;
        c1 = n1;
        c2 = n2;
        c3 = n3;

        i += 1;
    }

    min_i64(min_i64(c0, c1), min_i64(c2, c3))
}
