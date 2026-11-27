fn lower_bound(a: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = a.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if a[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

fn merge_sort(a: Vec<i64>) -> Vec<i64> {
    let n = a.len();
    if n <= 1 {
        return a;
    }

    let mut src = a;
    let mut dst: Vec<i64> = Vec::new();

    let mut z: usize = 0;
    while z < n {
        dst.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut l: usize = 0;

        while l < n {
            let mid: usize = if l + width < n { l + width } else { n };
            let r: usize = if l + width + width < n {
                l + width + width
            } else {
                n
            };

            let mut i = l;
            let mut j = mid;
            let mut k = l;

            while i < mid && j < r {
                if src[i] <= src[j] {
                    dst[k] = src[i];
                    i += 1;
                } else {
                    dst[k] = src[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                dst[k] = src[i];
                i += 1;
                k += 1;
            }

            while j < r {
                dst[k] = src[j];
                j += 1;
                k += 1;
            }

            l = r;
        }

        let mut c: usize = 0;
        while c < n {
            src[c] = dst[c];
            c += 1;
        }

        width = width * 2;
    }

    src
}

pub fn min_operations(nums: &[i64], queries: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        arr.push(nums[i]);
        i += 1;
    }

    let sorted = merge_sort(arr);

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);

    let mut i: usize = 0;
    while i < n {
        let next_sum = pref[i] + sorted[i];
        pref.push(next_sum);
        i += 1;
    }

    let total = pref[n];

    let mut ans: Vec<i64> = Vec::new();
    let m = queries.len();
    let mut qi: usize = 0;

    while qi < m {
        let q = queries[qi];
        let p = lower_bound(&sorted, q);

        let left_sum = pref[p];
        let right_sum = total - pref[p];

        let left_count = p as i64;
        let right_count = (n - p) as i64;

        let ops = q * left_count - left_sum + right_sum - q * right_count;
        ans.push(ops);

        qi += 1;
    }

    ans
}
