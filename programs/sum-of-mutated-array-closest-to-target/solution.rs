fn sum_after_mutate(arr: &[i64], value: i64) -> i64 {
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < arr.len() {
        if arr[i] < value {
            sum += arr[i];
        } else {
            sum += value;
        }
        i += 1;
    }
    sum
}

fn abs_diff(x: i64, y: i64) -> i64 {
    if x >= y {
        x - y
    } else {
        y - x
    }
}

pub fn find_best_value(arr: &[i64], target: i64) -> i64 {
    let mut max_val: i64 = 0;
    let mut i: usize = 0;
    while i < arr.len() {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = max_val;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        let s = sum_after_mutate(arr, mid);
        if s >= target {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }

    let candidate: i64 = lo;
    let mut best_value: i64 = candidate;
    let mut best_diff: i64 = abs_diff(sum_after_mutate(arr, candidate), target);

    if candidate > 0 {
        let other: i64 = candidate - 1;
        let other_diff: i64 = abs_diff(sum_after_mutate(arr, other), target);
        if other_diff < best_diff || (other_diff == best_diff && other < best_value) {
            best_diff = other_diff;
            best_value = other;
        }
    }

    best_value
}
