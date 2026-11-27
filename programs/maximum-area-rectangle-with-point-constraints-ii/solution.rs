const SHIFT: i64 = 100000001;

fn lower_bound(v: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn persistent_update(
    lc: &mut Vec<usize>,
    rc: &mut Vec<usize>,
    val: &mut Vec<i64>,
    prev: usize,
    size: usize,
    pos: usize,
    newval: i64,
) -> usize {
    let mut path: Vec<usize> = Vec::new();
    let mut dirs: Vec<bool> = Vec::new();

    let mut cur = prev;
    let mut l: usize = 0;
    let mut r: usize = size;

    while r - l > 1 {
        path.push(cur);
        let mid = (l + r) / 2;
        if pos < mid {
            dirs.push(true);
            cur = lc[cur];
            r = mid;
        } else {
            dirs.push(false);
            cur = rc[cur];
            l = mid;
        }
    }

    let mut new_idx = lc.len();
    lc.push(0);
    rc.push(0);
    val.push(newval);

    let mut k = dirs.len();
    while k > 0 {
        k -= 1;
        let old = path[k];
        let go_left = dirs[k];
        let node_idx = lc.len();

        if go_left {
            let sib = rc[old];
            let left_child = new_idx;
            lc.push(left_child);
            rc.push(sib);

            let lv = val[left_child];
            let sv = val[sib];
            if lv > sv {
                val.push(lv);
            } else {
                val.push(sv);
            }
        } else {
            let sib = lc[old];
            let right_child = new_idx;
            lc.push(sib);
            rc.push(right_child);

            let sv = val[sib];
            let rv = val[right_child];
            if rv > sv {
                val.push(rv);
            } else {
                val.push(sv);
            }
        }

        new_idx = node_idx;
    }

    new_idx
}

fn point_query(
    lc: &[usize],
    rc: &[usize],
    val: &[i64],
    root: usize,
    size: usize,
    pos: usize,
) -> i64 {
    let mut cur = root;
    let mut l: usize = 0;
    let mut r: usize = size;

    while r - l > 1 {
        if cur == 0 {
            return -1;
        }
        let mid = (l + r) / 2;
        if pos < mid {
            cur = lc[cur];
            r = mid;
        } else {
            cur = rc[cur];
            l = mid;
        }
    }

    if cur == 0 {
        -1
    } else {
        val[cur]
    }
}

fn range_max(
    lc: &[usize],
    rc: &[usize],
    val: &[i64],
    root: usize,
    size: usize,
    ql: usize,
    qr: usize,
) -> i64 {
    if ql >= qr {
        return -1;
    }

    let mut res: i64 = -1;

    let mut nodes: Vec<usize> = Vec::new();
    let mut lefts: Vec<usize> = Vec::new();
    let mut rights: Vec<usize> = Vec::new();

    nodes.push(root);
    lefts.push(0);
    rights.push(size);

    while nodes.len() > 0 {
        let last = nodes.len() - 1;
        let node = nodes[last];
        let l = lefts[last];
        let r = rights[last];

        let _ = nodes.pop();
        let _ = lefts.pop();
        let _ = rights.pop();

        if node == 0 {
            // Empty subtree.
        } else if qr <= l || r <= ql {
            // No overlap.
        } else if ql <= l && r <= qr {
            let v = val[node];
            if v > res {
                res = v;
            }
        } else {
            let mid = (l + r) / 2;
            let left_node = lc[node];
            let right_node = rc[node];

            nodes.push(left_node);
            lefts.push(l);
            rights.push(mid);

            nodes.push(right_node);
            lefts.push(mid);
            rights.push(r);
        }
    }

    res
}

pub fn max_rectangle_area(xCoord: &[i64], yCoord: &[i64]) -> i64 {
    let n = xCoord.len();
    if n < 4 {
        return -1;
    }

    let mut pts: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        pts.push(xCoord[i] * SHIFT + yCoord[i]);
        i += 1;
    }
    pts.sort();

    let mut unique_pts: Vec<i64> = Vec::new();
    i = 0;
    while i < pts.len() {
        let v = pts[i];
        unique_pts.push(v);
        i += 1;
        while i < pts.len() && pts[i] == v {
            i += 1;
        }
    }

    if unique_pts.len() < 4 {
        return -1;
    }

    let mut ys: Vec<i64> = Vec::new();
    i = 0;
    while i < unique_pts.len() {
        ys.push(unique_pts[i] % SHIFT);
        i += 1;
    }
    ys.sort();

    let mut unique_y: Vec<i64> = Vec::new();
    i = 0;
    while i < ys.len() {
        let v = ys[i];
        unique_y.push(v);
        i += 1;
        while i < ys.len() && ys[i] == v {
            i += 1;
        }
    }

    let m = unique_y.len();
    let mut size: usize = 1;
    while size < m {
        size *= 2;
    }

    let mut lc: Vec<usize> = Vec::new();
    let mut rc: Vec<usize> = Vec::new();
    let mut val: Vec<i64> = Vec::new();

    lc.push(0);
    rc.push(0);
    val.push(-1);

    let mut root: usize = 0;
    let mut ans: i64 = -1;

    let npts = unique_pts.len();
    let mut i: usize = 0;

    while i < npts {
        let key = unique_pts[i];
        let x = key / SHIFT;

        let mut j = i;
        while j < npts && unique_pts[j] / SHIFT == x {
            j += 1;
        }

        let mut k = i;
        while k + 1 < j {
            let y1 = unique_pts[k] % SHIFT;
            let y2 = unique_pts[k + 1] % SHIFT;

            let a = lower_bound(&unique_y, y1);
            let b = lower_bound(&unique_y, y2);

            let mx = range_max(&lc, &rc, &val, root, size, a, b + 1);

            if mx >= 0 {
                let la = point_query(&lc, &rc, &val, root, size, a);
                let lb = point_query(&lc, &rc, &val, root, size, b);

                if la == mx && lb == mx {
                    let inner = range_max(&lc, &rc, &val, root, size, a + 1, b);
                    if inner < mx {
                        let area = (x - mx) * (y2 - y1);
                        if area > ans {
                            ans = area;
                        }
                    }
                }
            }

            k += 1;
        }

        k = i;
        while k < j {
            let y = unique_pts[k] % SHIFT;
            let pos = lower_bound(&unique_y, y);
            root = persistent_update(&mut lc, &mut rc, &mut val, root, size, pos, x);
            k += 1;
        }

        i = j;
    }

    ans
}
