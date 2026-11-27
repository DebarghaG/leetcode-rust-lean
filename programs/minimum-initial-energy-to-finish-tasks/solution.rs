pub fn minimum_effort(tasks: &[Vec<i64>]) -> i64 {
    let n: usize = tasks.len();

    // Flatten tasks into [actual0, minimum0, actual1, minimum1, ...]
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(tasks[i][0]);
        v.push(tasks[i][1]);
        i += 1;
    }

    // Bottom-up merge sort by (minimum - actual) descending.
    let mut width: usize = 1;
    while width < n {
        let mut out: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid: usize = start + width;
            if mid > n {
                mid = n;
            }

            let mut end: usize = start + width + width;
            if end > n {
                end = n;
            }

            let mut left: usize = start;
            let mut right: usize = mid;

            while left < mid && right < end {
                let dl: i64 = v[2 * left + 1] - v[2 * left];
                let dr: i64 = v[2 * right + 1] - v[2 * right];

                if dl >= dr {
                    out.push(v[2 * left]);
                    out.push(v[2 * left + 1]);
                    left += 1;
                } else {
                    out.push(v[2 * right]);
                    out.push(v[2 * right + 1]);
                    right += 1;
                }
            }

            while left < mid {
                out.push(v[2 * left]);
                out.push(v[2 * left + 1]);
                left += 1;
            }

            while right < end {
                out.push(v[2 * right]);
                out.push(v[2 * right + 1]);
                right += 1;
            }

            start = end;
        }

        v = out;
        width = width + width;
    }

    // In the optimal order, the needed initial energy is
    // max over tasks of (minimum_i + sum of actual of previous tasks).
    let mut energy: i64 = 0;
    let mut spent: i64 = 0;
    let mut j: usize = 0;

    while j < n {
        let actual: i64 = v[2 * j];
        let minimum: i64 = v[2 * j + 1];
        let need: i64 = minimum + spent;

        if need > energy {
            energy = need;
        }

        spent = spent + actual;
        j += 1;
    }

    energy
}
