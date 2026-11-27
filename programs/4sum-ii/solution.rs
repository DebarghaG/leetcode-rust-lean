fn merge_sort(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        tmp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = mid + width;
            if right > n {
                right = n;
            }

            let mut i: usize = left;
            let mut j: usize = mid;
            let mut k: usize = left;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    tmp[k] = v[i];
                    i += 1;
                } else {
                    tmp[k] = v[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = v[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp[k] = v[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut t: usize = 0;
        while t < n {
            v[t] = tmp[t];
            t += 1;
        }

        width = width * 2;
    }

    v
}

pub fn four_sum_count(nums1: &[i64], nums2: &[i64], nums3: &[i64], nums4: &[i64]) -> i64 {
    let n = nums1.len();

    let mut sums12: Vec<i64> = Vec::new();
    let mut sums34: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            sums12.push(nums1[i] + nums2[j]);
            sums34.push(nums3[i] + nums4[j]);
            j += 1;
        }
        i += 1;
    }

    sums12 = merge_sort(sums12);
    sums34 = merge_sort(sums34);

    let m = sums12.len();
    let mut ans: i64 = 0;

    let mut i2: usize = 0;
    let mut j2: usize = m;

    while i2 < m {
        let x = sums12[i2];

        let mut i_end: usize = i2 + 1;
        let mut cntx: i64 = 1;
        while i_end < m && sums12[i_end] == x {
            i_end += 1;
            cntx += 1;
        }

        let target = -x;

        while j2 > 0 && sums34[j2 - 1] > target {
            j2 -= 1;
        }

        let mut cnty: i64 = 0;
        while j2 > 0 && sums34[j2 - 1] == target {
            j2 -= 1;
            cnty += 1;
        }

        ans += cntx * cnty;
        i2 = i_end;
    }

    ans
}
