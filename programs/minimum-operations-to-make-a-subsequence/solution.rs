pub fn min_operations(target: &[i64], arr: &[i64]) -> i64 {
    let n = target.len();
    if n == 0 {
        return 0;
    }

    // Build pairs (target value, original target index), stored in two parallel vectors.
    let mut vals: Vec<i64> = Vec::new();
    let mut idxs: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        vals.push(target[i]);
        idxs.push(i as i64);
        i += 1;
    }

    // Bottom-up merge sort of vals, keeping idxs aligned.
    let mut width = 1usize;
    while width < n {
        let mut temp_vals: Vec<i64> = Vec::new();
        let mut temp_idxs: Vec<i64> = Vec::new();

        let mut start = 0usize;
        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };
            let end = if mid + width < n {
                mid + width
            } else {
                n
            };

            let mut l = start;
            let mut r = mid;

            while l < mid && r < end {
                if vals[l] <= vals[r] {
                    temp_vals.push(vals[l]);
                    temp_idxs.push(idxs[l]);
                    l += 1;
                } else {
                    temp_vals.push(vals[r]);
                    temp_idxs.push(idxs[r]);
                    r += 1;
                }
            }

            while l < mid {
                temp_vals.push(vals[l]);
                temp_idxs.push(idxs[l]);
                l += 1;
            }

            while r < end {
                temp_vals.push(vals[r]);
                temp_idxs.push(idxs[r]);
                r += 1;
            }

            start = end;
        }

        vals = temp_vals;
        idxs = temp_idxs;
        width = width * 2;
    }

    // Convert arr into its target indices, ignoring values not present in target.
    // Then compute the length of the longest strictly increasing subsequence.
    let mut tails: Vec<i64> = Vec::new();

    let m = arr.len();
    let mut j = 0usize;
    while j < m {
        let x = arr[j];

        // Binary search for x in sorted vals.
        let mut lo = 0usize;
        let mut hi = n;
        let mut found = false;
        let mut pos = 0usize;

        while lo < hi {
            let mid = (lo + hi) / 2;
            if vals[mid] < x {
                lo = mid + 1;
            } else if vals[mid] > x {
                hi = mid;
            } else {
                pos = mid;
                found = true;
                break;
            }
        }

        if found {
            let target_index = idxs[pos];

            // Lower bound: first position in tails with tails[k] >= target_index.
            let len = tails.len();
            let mut l = 0usize;
            let mut r = len;

            while l < r {
                let mid = (l + r) / 2;
                if tails[mid] < target_index {
                    l = mid + 1;
                } else {
                    r = mid;
                }
            }

            if l == len {
                tails.push(target_index);
            } else {
                tails[l] = target_index;
            }
        }

        j += 1;
    }

    let lis_len = tails.len() as i64;
    (n as i64) - lis_len
}
