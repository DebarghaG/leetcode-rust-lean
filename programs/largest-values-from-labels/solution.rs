pub fn largest_vals_from_labels(values: &[i64], labels: &[i64], numWanted: i64, useLimit: i64) -> i64 {
    let n = values.len();
    if n == 0 || numWanted <= 0 || useLimit <= 0 {
        return 0;
    }

    let mut max_value: i64 = 0;
    let mut max_label: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let value = values[i];
        if value > max_value {
            max_value = value;
        }

        let label = labels[i];
        if label > max_label {
            max_label = label;
        }

        i += 1;
    }

    let num_buckets: usize = (max_value as usize) + 1;
    let mut buckets: Vec<Vec<i64>> = Vec::new();

    let mut b: usize = 0;
    while b < num_buckets {
        buckets.push(Vec::new());
        b += 1;
    }

    i = 0;
    while i < n {
        let value = values[i];
        let idx = value as usize;
        let label = labels[i];
        buckets[idx].push(label);
        i += 1;
    }

    let num_labels: usize = (max_label as usize) + 1;
    let mut used: Vec<i64> = Vec::new();

    let mut c: usize = 0;
    while c < num_labels {
        used.push(0);
        c += 1;
    }

    let mut remaining: i64 = numWanted;
    let mut total: i64 = 0;

    let mut vi: usize = num_buckets;
    while vi > 0 && remaining > 0 {
        vi -= 1;
        let value = vi as i64;
        let bucket_len = buckets[vi].len();

        let mut k: usize = 0;
        while k < bucket_len && remaining > 0 {
            let label = buckets[vi][k];
            let li = label as usize;

            if used[li] < useLimit {
                used[li] += 1;
                total += value;
                remaining -= 1;
            }

            k += 1;
        }
    }

    total
}
