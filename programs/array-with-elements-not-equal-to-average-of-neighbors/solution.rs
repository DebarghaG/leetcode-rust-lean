pub fn rearrange_array(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut v: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    // Bottom-up merge sort.
    let mut width: usize = 1;
    while width < n {
        let mut tmp: Vec<i64> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if mid + width < n { mid + width } else { n };

            let mut a = left;
            let mut b = mid;

            while a < mid && b < right {
                if v[a] <= v[b] {
                    tmp.push(v[a]);
                    a += 1;
                } else {
                    tmp.push(v[b]);
                    b += 1;
                }
            }

            while a < mid {
                tmp.push(v[a]);
                a += 1;
            }

            while b < right {
                tmp.push(v[b]);
                b += 1;
            }

            left = right;
        }

        v = tmp;
        width = width * 2;
    }

    let mid = (n + 1) / 2;
    let mut out: Vec<i64> = Vec::new();
    let mut k = 0;

    while k < n {
        if k % 2 == 0 {
            out.push(v[k / 2]);
        } else {
            out.push(v[mid + k / 2]);
        }
        k += 1;
    }

    out
}
