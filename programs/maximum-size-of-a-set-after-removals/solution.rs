fn count_distinct_sorted(v: &[i64]) -> i64 {
    let n = v.len();
    if n == 0 {
        return 0;
    }

    let mut count: i64 = 1;
    let mut i: usize = 1;
    while i < n {
        if v[i] != v[i - 1] {
            count += 1;
        }
        i += 1;
    }
    count
}

fn sort_vec(mut a: Vec<i64>) -> Vec<i64> {
    let n = a.len();

    let mut b: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        b.push(0);
        j += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let step = width * 2;
        let mut i: usize = 0;

        while i < n {
            let mid = if i + width < n { i + width } else { n };
            let end = if i + step < n { i + step } else { n };

            let mut l = i;
            let mut r = mid;
            let mut k = i;

            while l < mid && r < end {
                if a[l] <= a[r] {
                    b[k] = a[l];
                    l += 1;
                } else {
                    b[k] = a[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                b[k] = a[l];
                l += 1;
                k += 1;
            }

            while r < end {
                b[k] = a[r];
                r += 1;
                k += 1;
            }

            i = end;
        }

        let mut t: usize = 0;
        while t < n {
            a[t] = b[t];
            t += 1;
        }

        width = step;
    }

    a
}

fn sort_copy(xs: &[i64]) -> Vec<i64> {
    let n = xs.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        a.push(xs[i]);
        i += 1;
    }

    sort_vec(a)
}

pub fn maximum_set_size(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n_usize = nums1.len();
    let n = n_usize as i64;
    let half = (n_usize / 2) as i64;

    let a = sort_copy(nums1);
    let b = sort_copy(nums2);

    let d1 = count_distinct_sorted(&a);
    let d2 = count_distinct_sorted(&b);

    let mut all: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nums1.len() {
        all.push(nums1[i]);
        i += 1;
    }

    let mut j: usize = 0;
    while j < nums2.len() {
        all.push(nums2[j]);
        j += 1;
    }

    let all_sorted = sort_vec(all);
    let d_union = count_distinct_sorted(&all_sorted);

    let mut take1 = d1;
    if take1 > half {
        take1 = half;
    }

    let mut take2 = d2;
    if take2 > half {
        take2 = half;
    }

    let mut ans = take1 + take2;

    if ans > n {
        ans = n;
    }
    if ans > d_union {
        ans = d_union;
    }

    ans
}
