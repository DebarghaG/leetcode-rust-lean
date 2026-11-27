pub fn array_pair_sum(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        tmp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
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

            let mut a = start;
            let mut b = mid;
            let mut k = start;

            while a < mid && b < end {
                if v[a] <= v[b] {
                    tmp[k] = v[a];
                    a += 1;
                } else {
                    tmp[k] = v[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp[k] = v[a];
                a += 1;
                k += 1;
            }

            while b < end {
                tmp[k] = v[b];
                b += 1;
                k += 1;
            }

            start = end;
        }

        let mut j: usize = 0;
        while j < n {
            v[j] = tmp[j];
            j += 1;
        }

        width = width * 2;
    }

    let mut sum: i64 = 0;
    let mut p: usize = 0;
    while p < n {
        sum += v[p];
        p += 2;
    }

    sum
}
