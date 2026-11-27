pub fn max_area(height: &[i64]) -> i64 {
    let n = height.len();
    if n < 2 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut best: i64 = 0;

    while left < right {
        let lh = height[left];
        let rh = height[right];

        let h = if lh < rh { lh } else { rh };
        let width = (right - left) as i64;
        let area = h * width;

        if area > best {
            best = area;
        }

        if lh < rh {
            left = left + 1;
        } else {
            right = right - 1;
        }
    }

    best
}
