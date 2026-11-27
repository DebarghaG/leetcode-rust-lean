fn sort_i64(mut a: Vec<i64>) -> Vec<i64> {
    let n = a.len();
    if n <= 1 {
        return a;
    }

    let mut buf: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        buf.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;
        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };

            let end = if start + width + width < n {
                start + width + width
            } else {
                n
            };

            let mut l = start;
            let mut r = mid;
            let mut k = start;

            while l < mid && r < end {
                if a[l] <= a[r] {
                    buf[k] = a[l];
                    l += 1;
                } else {
                    buf[k] = a[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                buf[k] = a[l];
                l += 1;
                k += 1;
            }

            while r < end {
                buf[k] = a[r];
                r += 1;
                k += 1;
            }

            start = end;
        }

        i = 0;
        while i < n {
            a[i] = buf[i];
            i += 1;
        }

        width = width * 2;
    }

    a
}

fn lower_bound(xs: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = xs.len();

    while lo < hi {
        let mid = (lo + hi) / 2;
        if xs[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

pub fn maximum_sum_queries(nums1: &[i64], nums2: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = nums1.len();
    let qn = queries.len();

    let mut ys_all: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        ys_all.push(nums2[i]);
        i += 1;
    }

    let ys_sorted = sort_i64(ys_all);

    let mut ys: Vec<i64> = Vec::new();
    i = 0;
    while i < ys_sorted.len() {
        if i == 0 || ys_sorted[i] != ys_sorted[i - 1] {
            ys.push(ys_sorted[i]);
        }
        i += 1;
    }

    let m = ys.len();

    let mut size: usize = 1;
    while size < m {
        size = size * 2;
    }

    let total = size * 2;
    let mut tree: Vec<i64> = Vec::new();
    i = 0;
    while i < total {
        tree.push(-1);
        i += 1;
    }

    let pm: i64 = (n as i64) + 1;
    let mut pts: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        pts.push(nums1[i] * pm + (i as i64));
        i += 1;
    }
    let pts_sorted = sort_i64(pts);

    let qm: i64 = (qn as i64) + 1;
    let mut qs: Vec<i64> = Vec::new();
    i = 0;
    while i < qn {
        qs.push(queries[i][0] * qm + (i as i64));
        i += 1;
    }
    let qs_sorted = sort_i64(qs);

    let mut ans: Vec<i64> = Vec::new();
    i = 0;
    while i < qn {
        ans.push(-1);
        i += 1;
    }

    let mut p: usize = n;
    let mut k: usize = qn;

    while k > 0 {
        k -= 1;

        let qenc = qs_sorted[k];
        let qi = (qenc % qm) as usize;
        let x = queries[qi][0];
        let y = queries[qi][1];

        while p > 0 {
            let penc = pts_sorted[p - 1];
            let idx = (penc % pm) as usize;

            if nums1[idx] < x {
                break;
            }

            p -= 1;

            let yval = nums2[idx];
            let sum = nums1[idx] + yval;
            let r = lower_bound(&ys, yval);

            let mut pos = r + size;
            if sum > tree[pos] {
                tree[pos] = sum;
                let mut node = pos / 2;
                while node > 0 {
                    let left = tree[node * 2];
                    let right = tree[node * 2 + 1];
                    let best = if left > right { left } else { right };
                    tree[node] = best;
                    node = node / 2;
                }
            }
        }

        let r = lower_bound(&ys, y);
        if r < m {
            let mut best: i64 = -1;
            let mut left = r + size;
            let mut right = m + size;

            while left < right {
                if left % 2 == 1 {
                    if tree[left] > best {
                        best = tree[left];
                    }
                    left += 1;
                }

                if right % 2 == 1 {
                    right -= 1;
                    if tree[right] > best {
                        best = tree[right];
                    }
                }

                left = left / 2;
                right = right / 2;
            }

            ans[qi] = best;
        } else {
            ans[qi] = -1;
        }
    }

    ans
}
