pub fn min_operations(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i = i + 1;
    }

    let len = v.len();

    // Build a max heap.
    let mut start = len / 2;
    while start > 0 {
        start = start - 1;

        let end = len;
        let mut root = start;
        let mut done = false;

        while !done && root * 2 + 1 < end {
            let mut child = root * 2 + 1;

            if child + 1 < end && v[child] < v[child + 1] {
                child = child + 1;
            }

            if v[root] < v[child] {
                let tmp = v[root];
                v[root] = v[child];
                v[child] = tmp;
                root = child;
            } else {
                done = true;
            }
        }
    }

    // Extract elements from the heap to get ascending order.
    let mut end = len;
    while end > 1 {
        end = end - 1;

        let tmp = v[0];
        v[0] = v[end];
        v[end] = tmp;

        let mut root: usize = 0;
        let mut done = false;

        while !done && root * 2 + 1 < end {
            let mut child = root * 2 + 1;

            if child + 1 < end && v[child] < v[child + 1] {
                child = child + 1;
            }

            if v[root] < v[child] {
                let tmp2 = v[root];
                v[root] = v[child];
                v[child] = tmp2;
                root = child;
            } else {
                done = true;
            }
        }
    }

    // Deduplicate sorted values.
    let mut u: Vec<i64> = Vec::new();
    let mut last: i64 = 0;
    let mut has_last: bool = false;

    let mut j: usize = 0;
    while j < len {
        let val = v[j];

        if !has_last {
            u.push(val);
            last = val;
            has_last = true;
        } else if val != last {
            u.push(val);
            last = val;
        }

        j = j + 1;
    }

    let n_i64 = n as i64;
    let limit = n_i64 - 1;

    let m = u.len();
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut best: i64 = 0;

    // Largest number of distinct existing values fitting in an interval
    // of length n - 1.
    while right < m {
        while u[right] - u[left] > limit {
            left = left + 1;
        }

        let count = (right - left + 1) as i64;
        if count > best {
            best = count;
        }

        right = right + 1;
    }

    n_i64 - best
}
