pub fn get_strongest(arr: &[i64], k: i64) -> Vec<i64> {
    let n = arr.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(arr[i]);
        i += 1;
    }

    sorted.sort();

    let median_index = (n - 1) / 2;
    let median = sorted[median_index];

    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut out: Vec<i64> = Vec::new();
    let target: usize = k as usize;

    while out.len() < target && left <= right {
        if left == right {
            out.push(sorted[left]);
            break;
        }

        let left_value = sorted[left];
        let right_value = sorted[right];

        let mut left_diff = left_value - median;
        if left_diff < 0 {
            left_diff = -left_diff;
        }

        let mut right_diff = right_value - median;
        if right_diff < 0 {
            right_diff = -right_diff;
        }

        if left_diff > right_diff {
            out.push(left_value);
            left += 1;
        } else {
            out.push(right_value);
            right -= 1;
        }
    }

    out
}
