pub fn array_rank_transform(arr: &[i64]) -> Vec<i64> {
    let n: usize = arr.len();
    let mut result: Vec<i64> = Vec::new();

    if n == 0 {
        return result;
    }

    // Copy input into an owned vector.
    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(arr[i]);
        i += 1;
    }

    // Iterative bottom-up merge sort.
    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mid: usize = if start + width < n {
                start + width
            } else {
                n
            };

            let end: usize = if start + width + width < n {
                start + width + width
            } else {
                n
            };

            let mut p: usize = start;
            let mut q: usize = mid;

            while p < mid && q < end {
                if sorted[p] <= sorted[q] {
                    merged.push(sorted[p]);
                    p += 1;
                } else {
                    merged.push(sorted[q]);
                    q += 1;
                }
            }

            while p < mid {
                merged.push(sorted[p]);
                p += 1;
            }

            while q < end {
                merged.push(sorted[q]);
                q += 1;
            }

            start = end;
        }

        sorted = merged;
        width = width * 2;
    }

    // Build the sorted list of unique values.
    let mut unique: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if i == 0 || sorted[i] != sorted[i - 1] {
            unique.push(sorted[i]);
        }
        i += 1;
    }

    // For each original value, find its lower-bound position in unique values.
    i = 0;
    while i < n {
        let target: i64 = arr[i];
        let mut lo: usize = 0;
        let mut hi: usize = unique.len();

        while lo < hi {
            let mid: usize = lo + (hi - lo) / 2;
            if unique[mid] < target {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }

        result.push(lo as i64 + 1);
        i += 1;
    }

    result
}
