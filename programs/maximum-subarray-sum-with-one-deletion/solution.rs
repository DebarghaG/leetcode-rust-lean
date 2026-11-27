pub fn maximum_sum(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    let neg_inf: i64 = -1000000000000000000;

    // Maximum sum of a non-empty subarray ending at the current position
    // without using the deletion.
    let mut keep: i64 = arr[0];

    // Maximum sum of a non-empty subarray ending at the current position
    // after using the one deletion.
    let mut del: i64 = neg_inf;

    let mut best: i64 = arr[0];

    let mut i: usize = 1;
    while i < n {
        let x = arr[i];
        let prev_keep = keep;

        let extend_keep = prev_keep + x;
        let new_keep = if x > extend_keep { x } else { extend_keep };

        let extend_del = del + x;
        let new_del = if extend_del > prev_keep { extend_del } else { prev_keep };

        keep = new_keep;
        del = new_del;

        if keep > best {
            best = keep;
        }
        if del > best {
            best = del;
        }

        i += 1;
    }

    best
}
