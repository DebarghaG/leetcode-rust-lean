pub fn maximize_win(prizePositions: &[i64], k: i64) -> i64 {
    let n = prizePositions.len();

    // best_prefix[i] = maximum prizes obtainable from the first i prizes
    // using at most one segment.
    let mut best_prefix: Vec<i64> = Vec::new();
    let mut t = 0usize;
    while t <= n {
        best_prefix.push(0);
        t += 1;
    }

    let mut left = 0usize;
    let mut right = 0usize;
    let mut ans = 0i64;

    while right < n {
        while left <= right && prizePositions[right] - prizePositions[left] > k {
            left += 1;
        }

        let count = (right - left + 1) as i64;

        // Use one segment before 'left' and one segment covering left..=right.
        let candidate = best_prefix[left] + count;
        if candidate > ans {
            ans = candidate;
        }

        // Update the best single segment over the prefix ending at right.
        let previous = best_prefix[right];
        if count > previous {
            best_prefix[right + 1] = count;
        } else {
            best_prefix[right + 1] = previous;
        }

        right += 1;
    }

    ans
}
