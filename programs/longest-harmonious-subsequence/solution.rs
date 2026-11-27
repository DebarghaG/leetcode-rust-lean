pub fn find_lhs(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    let mut v: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        v.push(nums[idx]);
        idx += 1;
    }

    if n == 0 {
        return 0;
    }

    // Bottom-up merge sort to keep the implementation inside the safe subset.
    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut left: usize = 0;
        let two_width: usize = width + width;

        while left < n {
            let mid: usize = if left + width < n { left + width } else { n };
            let right: usize = if left + two_width < n { left + two_width } else { n };

            let mut i: usize = left;
            let mut j: usize = mid;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    merged.push(v[i]);
                    i += 1;
                } else {
                    merged.push(v[j]);
                    j += 1;
                }
            }

            while i < mid {
                merged.push(v[i]);
                i += 1;
            }

            while j < right {
                merged.push(v[j]);
                j += 1;
            }

            left = right;
        }

        v = merged;
        width = width + width;
    }

    let mut best: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i;
        let mut count_a: i64 = 0;

        while j < n && v[j] == v[i] {
            count_a += 1;
            j += 1;
        }

        if j < n && v[j] == v[i] + 1 {
            let mut k: usize = j;
            let mut count_b: i64 = 0;

            while k < n && v[k] == v[j] {
                count_b += 1;
                k += 1;
            }

            let total: i64 = count_a + count_b;
            if total > best {
                best = total;
            }
        }

        i = j;
    }

    best
}
