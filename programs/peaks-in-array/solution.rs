fn is_peak(a: &[i64], i: usize) -> bool {
    let n = a.len();
    if i == 0 || i + 1 >= n {
        false
    } else {
        a[i] > a[i - 1] && a[i] > a[i + 1]
    }
}

fn seg_query(tree: &[i64], size: usize, mut l: usize, mut r: usize) -> i64 {
    l += size;
    r += size;
    let mut res = 0;
    while l < r {
        if l % 2 == 1 {
            res += tree[l];
            l += 1;
        }
        if r % 2 == 1 {
            r -= 1;
            res += tree[r];
        }
        l /= 2;
        r /= 2;
    }
    res
}

pub fn count_of_peaks(nums: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let size = n;
    let mut tree: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < 2 * size {
        tree.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        if is_peak(&a, i) {
            tree[size + i] = 1;
        }
        i += 1;
    }

    let mut p = size;
    while p > 1 {
        p -= 1;
        tree[p] = tree[2 * p] + tree[2 * p + 1];
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut qi = 0;
    while qi < queries.len() {
        let q = &queries[qi];

        if q[0] == 1 {
            let l = q[1] as usize;
            let r = q[2] as usize;

            if r <= l + 1 {
                ans.push(0);
            } else {
                let cnt = seg_query(&tree, size, l + 1, r);
                ans.push(cnt);
            }
        } else {
            let idx = q[1] as usize;
            let val = q[2];

            if a[idx] != val {
                a[idx] = val;

                let mut k = 0;
                while k < 3 {
                    let mut c = idx;
                    let mut ok = true;

                    if k == 0 {
                        if idx > 0 {
                            c = idx - 1;
                        } else {
                            ok = false;
                        }
                    } else if k == 1 {
                        c = idx;
                    } else {
                        if idx + 1 < n {
                            c = idx + 1;
                        } else {
                            ok = false;
                        }
                    }

                    if ok {
                        let v = if is_peak(&a, c) { 1 } else { 0 };
                        let mut pos = size + c;
                        tree[pos] = v;
                        pos /= 2;
                        while pos > 0 {
                            tree[pos] = tree[2 * pos] + tree[2 * pos + 1];
                            pos /= 2;
                        }
                    }

                    k += 1;
                }
            }
        }

        qi += 1;
    }

    ans
}
