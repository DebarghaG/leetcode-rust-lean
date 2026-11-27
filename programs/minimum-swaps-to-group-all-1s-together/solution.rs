pub fn min_swaps(data: &[i64]) -> i64 {
    let n = data.len();

    let mut total_ones: usize = 0;
    let mut i: usize = 0;
    while i < n {
        if data[i] == 1 {
            total_ones += 1;
        }
        i += 1;
    }

    if total_ones <= 1 {
        return 0;
    }

    let k = total_ones;

    let mut current_ones: usize = 0;
    let mut j: usize = 0;
    while j < k {
        if data[j] == 1 {
            current_ones += 1;
        }
        j += 1;
    }

    let mut max_ones = current_ones;

    let mut start: usize = 1;
    while start + k <= n {
        if data[start - 1] == 1 {
            current_ones -= 1;
        }
        if data[start + k - 1] == 1 {
            current_ones += 1;
        }
        if current_ones > max_ones {
            max_ones = current_ones;
        }
        start += 1;
    }

    (total_ones - max_ones) as i64
}
