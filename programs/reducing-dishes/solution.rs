pub fn max_satisfaction(satisfaction: &[i64]) -> i64 {
    let n = satisfaction.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(satisfaction[i]);
        i += 1;
    }

    // Insertion sort in non-decreasing order.
    let mut i = 1;
    while i < n {
        let key = a[i];
        let mut j = i;

        while j > 0 {
            if a[j - 1] <= key {
                break;
            }
            a[j] = a[j - 1];
            j -= 1;
        }

        a[j] = key;
        i += 1;
    }

    let mut suffix_sum: i64 = 0;
    let mut total: i64 = 0;

    let mut i = n;
    while i > 0 {
        i -= 1;
        suffix_sum += a[i];
        if suffix_sum > 0 {
            total += suffix_sum;
        }
    }

    total
}
