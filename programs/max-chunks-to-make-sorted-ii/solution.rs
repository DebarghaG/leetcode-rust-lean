pub fn max_chunks_to_sorted(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    let mut suffix_min: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        suffix_min.push(0);
        i += 1;
    }

    let mut cur_min = arr[n - 1];
    let mut j = n;
    while j > 0 {
        let idx = j - 1;
        if arr[idx] < cur_min {
            cur_min = arr[idx];
        }
        suffix_min[idx] = cur_min;
        j = idx;
    }

    let mut chunks: i64 = 0;
    let mut prefix_max = arr[0];
    let mut k: usize = 0;
    while k < n {
        if arr[k] > prefix_max {
            prefix_max = arr[k];
        }

        if k + 1 == n || prefix_max <= suffix_min[k + 1] {
            chunks += 1;
        }

        k += 1;
    }

    chunks
}
