pub fn get_distances(arr: &[i64]) -> Vec<i64> {
    let n = arr.len();
    if n == 0 {
        return Vec::new();
    }

    // Find the maximum value to size the counting array.
    let mut max_val = arr[0];
    let mut i = 1;
    while i < n {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i += 1;
    }

    let size = (max_val + 2) as usize;
    let mut count: Vec<i64> = Vec::new();
    let mut v = 0;
    while v < size {
        count.push(0);
        v += 1;
    }

    // Count frequencies (offset by one for prefix sums).
    i = 0;
    while i < n {
        let val = arr[i] as usize;
        count[val + 1] += 1;
        i += 1;
    }

    // Convert counts to starting positions.
    v = 1;
    while v < size {
        count[v] += count[v - 1];
        v += 1;
    }

    // Build an array of indices sorted by value (stable within equal values).
    let mut sorted_idx: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < n {
        sorted_idx.push(0);
        k += 1;
    }

    i = 0;
    while i < n {
        let val = arr[i] as usize;
        let p = count[val] as usize;
        sorted_idx[p] = i as i64;
        count[val] += 1;
        i += 1;
    }

    // Result array.
    let mut out: Vec<i64> = Vec::new();
    k = 0;
    while k < n {
        out.push(0);
        k += 1;
    }

    // Process each group of equal values in sorted_idx.
    i = 0;
    while i < n {
        let val = arr[sorted_idx[i] as usize];
        let mut j = i;
        let mut same = true;
        while j < n && same {
            if arr[sorted_idx[j] as usize] == val {
                j += 1;
            } else {
                same = false;
            }
        }

        // Group is [i, j) in sorted_idx.
        let mut total: i64 = 0;
        let mut t = i;
        while t < j {
            total += sorted_idx[t];
            t += 1;
        }

        let len = (j - i) as i64;
        let mut prefix: i64 = 0;
        let mut cnt: i64 = 0;
        t = i;
        while t < j {
            let idx = sorted_idx[t];
            let left = idx * cnt - prefix;
            let sum_after = total - prefix - idx;
            let right = sum_after - idx * (len - 1 - cnt);
            out[idx as usize] = left + right;
            prefix += idx;
            cnt += 1;
            t += 1;
        }

        i = j;
    }

    out
}
