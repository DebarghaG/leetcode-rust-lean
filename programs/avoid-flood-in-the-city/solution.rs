fn lower_bound_i64(v: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if v[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        temp.push(0);
        z += 1;
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

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if v[a] <= v[b] {
                    temp[k] = v[a];
                    a += 1;
                } else {
                    temp[k] = v[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                temp[k] = v[a];
                a += 1;
                k += 1;
            }

            while b < right {
                temp[k] = v[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        let mut p: usize = 0;
        while p < n {
            v[p] = temp[p];
            p += 1;
        }

        width = width * 2;
    }
}

fn seg_update(tree: &mut Vec<i64>, size: usize, idx: usize, val: i64) {
    let mut p = size + idx;
    tree[p] = val;
    p = p / 2;

    while p > 0 {
        tree[p] = tree[2 * p] + tree[2 * p + 1];
        p = p / 2;
    }
}

fn seg_prefix(tree: &[i64], size: usize, end: usize) -> i64 {
    let mut l = size;
    let mut r = size + end;
    let mut sum: i64 = 0;

    while l < r {
        if l % 2 == 1 {
            sum += tree[l];
            l += 1;
        }
        if r % 2 == 1 {
            r -= 1;
            sum += tree[r];
        }
        l = l / 2;
        r = r / 2;
    }

    sum
}

fn seg_kth(tree: &[i64], size: usize, k: i64) -> usize {
    let mut node: usize = 1;
    let mut kk: i64 = k;

    while node < size {
        let left = 2 * node;
        if tree[left] >= kk {
            node = left;
        } else {
            kk -= tree[left];
            node = left + 1;
        }
    }

    node - size
}

pub fn avoid_flood(rains: &[i64]) -> Vec<i64> {
    let n: usize = rains.len();

    let mut lakes: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        if rains[i] > 0 {
            lakes.push(rains[i]);
        }
        i += 1;
    }

    sort_i64(&mut lakes);

    let mut uniq: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < lakes.len() {
        if p == 0 {
            uniq.push(lakes[p]);
        } else {
            if lakes[p] != lakes[p - 1] {
                uniq.push(lakes[p]);
            }
        }
        p += 1;
    }

    let m = uniq.len();
    let mut last: Vec<usize> = Vec::new();
    let mut q: usize = 0;
    while q < m {
        last.push(n);
        q += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut a: usize = 0;
    while a < n {
        ans.push(1);
        a += 1;
    }

    let mut size: usize = 1;
    while size < n {
        size = size * 2;
    }

    let total_nodes = size * 2;
    let mut tree: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < total_nodes {
        tree.push(0);
        t += 1;
    }

    i = 0;
    while i < n {
        let r: i64 = rains[i];

        if r == 0 {
            ans[i] = 1;
            seg_update(&mut tree, size, i, 1);
        } else {
            ans[i] = -1;

            let pos = lower_bound_i64(&uniq, r);

            if last[pos] < n {
                let prev = last[pos];
                let before = seg_prefix(&tree, size, prev + 1);
                let active = tree[1];

                if before >= active {
                    return Vec::new();
                }

                let k = before + 1;
                let dry_idx = seg_kth(&tree, size, k);

                ans[dry_idx] = r;
                seg_update(&mut tree, size, dry_idx, 0);
            }

            last[pos] = i;
        }

        i += 1;
    }

    ans
}
