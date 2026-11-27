pub fn closest_room(rooms: &[Vec<i64>], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = rooms.len();
    let k = queries.len();

    // Extract ids and sizes in original order.
    let mut cur_ids: Vec<i64> = Vec::new();
    let mut cur_sizes: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        cur_ids.push(rooms[i][0]);
        cur_sizes.push(rooms[i][1]);
        i += 1;
    }

    // Bottom-up merge sort by id ascending, keeping sizes aligned.
    let mut width = 1usize;
    while width < n {
        let w2 = width + width;
        let mut next_ids: Vec<i64> = Vec::new();
        let mut next_sizes: Vec<i64> = Vec::new();
        let mut start = 0usize;
        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + w2 < n { start + w2 } else { n };
            let mut p = start;
            let mut q = mid;
            while p < mid && q < end {
                if cur_ids[p] <= cur_ids[q] {
                    next_ids.push(cur_ids[p]);
                    next_sizes.push(cur_sizes[p]);
                    p += 1;
                } else {
                    next_ids.push(cur_ids[q]);
                    next_sizes.push(cur_sizes[q]);
                    q += 1;
                }
            }
            while p < mid {
                next_ids.push(cur_ids[p]);
                next_sizes.push(cur_sizes[p]);
                p += 1;
            }
            while q < end {
                next_ids.push(cur_ids[q]);
                next_sizes.push(cur_sizes[q]);
                q += 1;
            }
            start = end;
        }
        cur_ids = next_ids;
        cur_sizes = next_sizes;
        width = w2;
    }

    let ids = cur_ids;
    let sizes = cur_sizes;

    // max_level = floor(log2(n)).
    let mut max_level = 0usize;
    let mut pv = 1usize;
    while pv + pv <= n {
        pv = pv + pv;
        max_level += 1;
    }

    // Sparse table of range maxima over sizes.
    let mut sp: Vec<Vec<i64>> = Vec::new();
    let mut row0: Vec<i64> = Vec::new();
    let mut j = 0usize;
    while j < n {
        row0.push(sizes[j]);
        j += 1;
    }
    sp.push(row0);

    let mut level = 1usize;
    let mut half = 1usize;
    while level <= max_level {
        let full = half + half;
        let count = n - full + 1;
        let mut row: Vec<i64> = Vec::new();
        let mut p = 0usize;
        while p < count {
            let a = sp[level - 1][p];
            let b = sp[level - 1][p + half];
            let m = if a > b { a } else { b };
            row.push(m);
            p += 1;
        }
        sp.push(row);
        half = full;
        level += 1;
    }

    // Answer queries.
    let mut ans: Vec<i64> = Vec::new();
    let mut q = 0usize;
    while q < k {
        let pref = queries[q][0];
        let min_size = queries[q][1];

        // First index with ids[index] > pref.
        let mut lo = 0usize;
        let mut hi = n;
        while lo < hi {
            let mid = (lo + hi) / 2;
            if ids[mid] <= pref {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let ub = lo;

        let mut best_id: i64 = -1;
        let mut best_diff: i64 = 0;
        let mut found = false;

        // Left side: indices [0, ub-1], find rightmost with size >= min_size.
        if ub > 0 {
            let hi_left = ub - 1;
            if range_max(&sp, 0, hi_left) >= min_size {
                let mut l = 0usize;
                let mut h = hi_left;
                while l < h {
                    let mid = (l + h + 1) / 2;
                    if range_max(&sp, mid, h) >= min_size {
                        l = mid;
                    } else {
                        h = mid - 1;
                    }
                }
                let cand = ids[l];
                let diff = pref - cand;
                best_id = cand;
                best_diff = diff;
                found = true;
            }
        }

        // Right side: indices [ub, n-1], find leftmost with size >= min_size.
        if ub < n {
            let lo_right = ub;
            let hi_right = n - 1;
            if range_max(&sp, lo_right, hi_right) >= min_size {
                let mut l = lo_right;
                let mut h = hi_right;
                while l < h {
                    let mid = (l + h) / 2;
                    if range_max(&sp, l, mid) >= min_size {
                        h = mid;
                    } else {
                        l = mid + 1;
                    }
                }
                let cand = ids[l];
                let diff = cand - pref;
                if !found || diff < best_diff || (diff == best_diff && cand < best_id) {
                    best_id = cand;
                    best_diff = diff;
                    found = true;
                }
            }
        }

        if found {
            ans.push(best_id);
        } else {
            ans.push(-1);
        }
        q += 1;
    }

    ans
}

fn range_max(sp: &[Vec<i64>], l: usize, r: usize) -> i64 {
    let len = r - l + 1;
    let mut p = 0usize;
    let mut pv = 1usize;
    while pv + pv <= len {
        pv = pv + pv;
        p += 1;
    }
    let a = sp[p][l];
    let b = sp[p][l + (len - pv)];
    if a > b { a } else { b }
}
