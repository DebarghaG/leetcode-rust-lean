pub fn rearrange_barcodes(barcodes: &[i64]) -> Vec<i64> {
    let n = barcodes.len();
    let mut res: Vec<i64> = Vec::new();
    if n == 0 {
        return res;
    }

    // Find the maximum barcode value.
    let mut max_val: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let v = barcodes[i];
        if v > max_val {
            max_val = v;
        }
        i += 1;
    }

    let m = (max_val as usize) + 1;

    // Count frequencies.
    let mut counts: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        counts.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        let v = barcodes[i];
        let idx = v as usize;
        counts[idx] = counts[idx] + 1;
        i += 1;
    }

    // Find the maximum frequency.
    let mut max_freq: i64 = 0;
    let mut v_idx: usize = 0;
    while v_idx < m {
        if counts[v_idx] > max_freq {
            max_freq = counts[v_idx];
        }
        v_idx += 1;
    }

    // buckets[f] stores all values with frequency f, in increasing value order.
    let bucket_count = (max_freq as usize) + 1;
    let mut buckets: Vec<Vec<i64>> = Vec::new();
    let mut b: usize = 0;
    while b < bucket_count {
        let empty: Vec<i64> = Vec::new();
        buckets.push(empty);
        b += 1;
    }

    v_idx = 0;
    while v_idx < m {
        let c = counts[v_idx];
        if c > 0 {
            let f = c as usize;
            let value = v_idx as i64;
            buckets[f].push(value);
        }
        v_idx += 1;
    }

    // Build the multiset sorted by frequency descending, then value ascending.
    let mut sorted: Vec<i64> = Vec::new();
    let mut freq = max_freq;
    while freq > 0 {
        let f = freq as usize;
        let bucket = &buckets[f];
        let blen = bucket.len();
        let mut k: usize = 0;
        while k < blen {
            let value = bucket[k];
            let mut rep: i64 = 0;
            while rep < freq {
                sorted.push(value);
                rep += 1;
            }
            k += 1;
        }
        freq -= 1;
    }

    // Initialize the result with zeros.
    let mut z: usize = 0;
    while z < n {
        res.push(0);
        z += 1;
    }

    // Fill even positions first, then odd positions.
    let mut idx: usize = 0;
    let mut pos: usize = 0;
    while pos < n {
        res[pos] = sorted[idx];
        idx += 1;
        pos += 2;
    }

    pos = 1;
    while pos < n {
        res[pos] = sorted[idx];
        idx += 1;
        pos += 2;
    }

    res
}
