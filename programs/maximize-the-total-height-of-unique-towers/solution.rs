pub fn maximum_total_sum(maximumHeight: &[i64]) -> i64 {
    let n = maximumHeight.len();
    if n == 0 {
        return 0;
    }

    let mut heights: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        heights.push(maximumHeight[i]);
        i += 1;
    }

    // Iterative merge sort in ascending order.
    let mut buf: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        buf.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right_bound = left + width + width;
            let right = if right_bound < n { right_bound } else { n };

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if heights[a] <= heights[b] {
                    buf[k] = heights[a];
                    a += 1;
                } else {
                    buf[k] = heights[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                buf[k] = heights[a];
                a += 1;
                k += 1;
            }

            while b < right {
                buf[k] = heights[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        i = 0;
        while i < n {
            heights[i] = buf[i];
            i += 1;
        }

        width = width + width;
    }

    let mut total: i64 = 0;
    let mut prev: i64 = 1_000_000_001;
    let mut j: usize = n;

    while j > 0 {
        j -= 1;
        let h = heights[j];
        let mut assigned = h;

        if assigned >= prev {
            assigned = prev - 1;
        }

        if assigned <= 0 {
            return -1;
        }

        total += assigned;
        prev = assigned;
    }

    total
}
