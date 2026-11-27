pub fn largest_perimeter(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut v: Vec<i64> = Vec::new();
    let mut i0 = 0;
    while i0 < n {
        v.push(nums[i0]);
        i0 += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut out: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + width + width;
            if end > n {
                end = n;
            }

            let mut i = start;
            let mut j = mid;

            while i < mid && j < end {
                if v[i] <= v[j] {
                    out.push(v[i]);
                    i += 1;
                } else {
                    out.push(v[j]);
                    j += 1;
                }
            }

            while i < mid {
                out.push(v[i]);
                i += 1;
            }

            while j < end {
                out.push(v[j]);
                j += 1;
            }

            start = end;
        }

        let mut k = 0;
        while k < n {
            v[k] = out[k];
            k += 1;
        }

        width = width + width;
    }

    let mut total: i64 = 0;
    let mut i = 0;
    while i < n {
        total += v[i];
        i += 1;
    }

    let mut k = n;
    while k >= 3 {
        let largest = v[k - 1];
        if total - largest > largest {
            return total;
        }
        total -= largest;
        k -= 1;
    }

    -1
}
