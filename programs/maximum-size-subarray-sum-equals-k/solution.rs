fn lower_bound(xs: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if xs[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

fn merge_sort_i64(a: &mut Vec<i64>) {
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        tmp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + width + width;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;
            let mut k = left;

            while i < mid && j < right {
                if a[i] <= a[j] {
                    tmp[k] = a[i];
                    i += 1;
                } else {
                    tmp[k] = a[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = a[i];
                i += 1;
                k += 1;
            }

            while j < right {
                tmp[k] = a[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut p: usize = 0;
        while p < n {
            a[p] = tmp[p];
            p += 1;
        }

        width = width + width;
    }
}

pub fn max_sub_array_len(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut pref: Vec<i64> = Vec::new();
    pref.push(0);

    let mut i: usize = 0;
    while i < n {
        let prev = pref[i];
        pref.push(prev + nums[i]);
        i += 1;
    }

    let m = n + 1;

    let mut sorted: Vec<i64> = Vec::new();
    let mut q: usize = 0;
    while q < m {
        sorted.push(pref[q]);
        q += 1;
    }

    merge_sort_i64(&mut sorted);

    let mut uniq: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < m {
        if j == 0 {
            uniq.push(sorted[j]);
        } else if sorted[j] != sorted[j - 1] {
            uniq.push(sorted[j]);
        }
        j += 1;
    }

    let u = uniq.len();
    let mut first: Vec<usize> = Vec::new();
    let mut z: usize = 0;
    while z < u {
        first.push(m);
        z += 1;
    }

    let mut idx: usize = 0;
    while idx < m {
        let val = pref[idx];
        let pos = lower_bound(&uniq, val);
        if first[pos] == m {
            first[pos] = idx;
        }
        idx += 1;
    }

    let mut ans: usize = 0;
    let mut end: usize = 0;

    while end < m {
        let target = pref[end] - k;
        let pos = lower_bound(&uniq, target);

        if pos < u && uniq[pos] == target {
            let start = first[pos];
            if start <= end {
                let len = end - start;
                if len > ans {
                    ans = len;
                }
            }
        }

        end += 1;
    }

    ans as i64
}
