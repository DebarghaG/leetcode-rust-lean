pub fn maximize_greatness(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        sorted.push(nums[idx]);
        idx += 1;
    }

    // Bottom-up merge sort.
    if n >= 2 {
        let mut tmp: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < n {
            tmp.push(0);
            k += 1;
        }

        let mut width: usize = 1;
        while width < n {
            let mut left: usize = 0;
            while left < n {
                let step = width * 2;
                let mid = if left + width < n { left + width } else { n };
                let right = if left + step < n { left + step } else { n };

                let mut i = left;
                let mut j = mid;
                let mut t = left;

                while i < mid && j < right {
                    if sorted[i] <= sorted[j] {
                        tmp[t] = sorted[i];
                        i += 1;
                    } else {
                        tmp[t] = sorted[j];
                        j += 1;
                    }
                    t += 1;
                }

                while i < mid {
                    tmp[t] = sorted[i];
                    i += 1;
                    t += 1;
                }

                while j < right {
                    tmp[t] = sorted[j];
                    j += 1;
                    t += 1;
                }

                left += step;
            }

            let mut p: usize = 0;
            while p < n {
                sorted[p] = tmp[p];
                p += 1;
            }

            width = width * 2;
        }
    }

    let mut i: usize = 0;
    let mut j: usize = 0;
    let mut count: i64 = 0;

    while i < n && j < n {
        if sorted[j] > sorted[i] {
            count += 1;
            i += 1;
            j += 1;
        } else {
            j += 1;
        }
    }

    count
}
