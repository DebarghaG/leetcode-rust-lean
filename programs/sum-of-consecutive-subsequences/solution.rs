pub fn get_sum(nums: &[i64]) -> i64 {
    let md: i64 = 1_000_000_007;
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    // Copy nums into an owned vector.
    let mut cur: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        cur.push(nums[i]);
        i += 1;
    }

    // Iterative bottom-up merge sort.
    let mut width: usize = 1;
    while width < n {
        let mut next: Vec<i64> = Vec::new();
        let mut start: usize = 0;
        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }
            let mut end = start + 2 * width;
            if end > n {
                end = n;
            }

            let mut a = start;
            let mut b = mid;
            while a < mid && b < end {
                if cur[a] <= cur[b] {
                    next.push(cur[a]);
                    a += 1;
                } else {
                    next.push(cur[b]);
                    b += 1;
                }
            }
            while a < mid {
                next.push(cur[a]);
                a += 1;
            }
            while b < end {
                next.push(cur[b]);
                b += 1;
            }
            start = end;
        }
        cur = next;
        width = width * 2;
    }

    // Build the sorted list of distinct values.
    let mut unique: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < n {
        let l = unique.len();
        if l == 0 || unique[l - 1] != cur[j] {
            unique.push(cur[j]);
        }
        j += 1;
    }
    let k: usize = unique.len();

    // Persistent segment tree over the compressed value indices.
    // Node 0 is the null / all-zero node.
    let mut left: Vec<usize> = Vec::new();
    let mut right: Vec<usize> = Vec::new();
    let mut vc1: Vec<i64> = Vec::new();
    let mut vss: Vec<i64> = Vec::new();
    let mut vic: Vec<i64> = Vec::new();
    let mut vis: Vec<i64> = Vec::new();
    let mut vdc: Vec<i64> = Vec::new();
    let mut vds: Vec<i64> = Vec::new();

    left.push(0);
    right.push(0);
    vc1.push(0);
    vss.push(0);
    vic.push(0);
    vis.push(0);
    vdc.push(0);
    vds.push(0);

    let mut root: usize = 0;
    let mut ans: i64 = 0;

    let mut idx_nums: usize = 0;
    while idx_nums < n {
        let x = nums[idx_nums];
        let xm = x % md;

        // Compressed index of x.
        let mut lo: usize = 0;
        let mut hi: usize = k;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if unique[mid] < x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let idx = lo;

        // Check whether x - 1 exists.
        let mut prev_valid: bool = false;
        let mut prev_idx: usize = 0;
        if idx > 0 {
            if unique[idx - 1] == x - 1 {
                prev_valid = true;
                prev_idx = idx - 1;
            }
        }

        // Check whether x + 1 exists.
        let mut next_valid: bool = false;
        let mut next_idx: usize = 0;
        let idxp1 = idx + 1;
        if idxp1 < k {
            if unique[idxp1] == x + 1 {
                next_valid = true;
                next_idx = idxp1;
            }
        }

        // New increasing sequences from x - 1.
        let mut new_inc_count: i64 = 0;
        let mut new_inc_sum: i64 = 0;
        if prev_valid {
            let mut node: usize = root;
            let mut l: usize = 0;
            let mut h: usize = k;
            while h - l > 1 {
                let mid = l + (h - l) / 2;
                if prev_idx < mid {
                    if node != 0 {
                        node = left[node];
                    }
                    h = mid;
                } else {
                    if node != 0 {
                        node = right[node];
                    }
                    l = mid;
                }
            }

            let mut c1p: i64 = 0;
            let mut ssp: i64 = 0;
            let mut icp: i64 = 0;
            let mut isp: i64 = 0;
            if node != 0 {
                c1p = vc1[node];
                ssp = vss[node];
                icp = vic[node];
                isp = vis[node];
            }
            let cnt = (c1p + icp) % md;
            let sum_prev = (ssp + isp) % md;
            new_inc_count = cnt;
            new_inc_sum = (sum_prev + xm * cnt) % md;
        }

        // New decreasing sequences from x + 1.
        let mut new_dec_count: i64 = 0;
        let mut new_dec_sum: i64 = 0;
        if next_valid {
            let mut node: usize = root;
            let mut l: usize = 0;
            let mut h: usize = k;
            while h - l > 1 {
                let mid = l + (h - l) / 2;
                if next_idx < mid {
                    if node != 0 {
                        node = left[node];
                    }
                    h = mid;
                } else {
                    if node != 0 {
                        node = right[node];
                    }
                    l = mid;
                }
            }

            let mut c1n: i64 = 0;
            let mut ssn: i64 = 0;
            let mut dcn: i64 = 0;
            let mut dsn: i64 = 0;
            if node != 0 {
                c1n = vc1[node];
                ssn = vss[node];
                dcn = vdc[node];
                dsn = vds[node];
            }
            let cnt = (c1n + dcn) % md;
            let sum_next = (ssn + dsn) % md;
            new_dec_count = cnt;
            new_dec_sum = (sum_next + xm * cnt) % md;
        }

        // Contribution of all consecutive subsequences ending at this occurrence.
        let contrib = (xm + new_inc_sum + new_dec_sum) % md;
        ans = (ans + contrib) % md;

        // Update the persistent tree at index idx.
        let mut path: Vec<usize> = Vec::new();
        let mut dirs: Vec<bool> = Vec::new();
        let mut node: usize = root;
        let mut l: usize = 0;
        let mut h: usize = k;
        while h - l > 1 {
            path.push(node);
            let mid = l + (h - l) / 2;
            if idx < mid {
                dirs.push(false);
                if node != 0 {
                    node = left[node];
                }
                h = mid;
            } else {
                dirs.push(true);
                if node != 0 {
                    node = right[node];
                }
                l = mid;
            }
        }

        let mut old_c1: i64 = 0;
        let mut old_ss: i64 = 0;
        let mut old_ic: i64 = 0;
        let mut old_is: i64 = 0;
        let mut old_dc: i64 = 0;
        let mut old_ds: i64 = 0;
        if node != 0 {
            old_c1 = vc1[node];
            old_ss = vss[node];
            old_ic = vic[node];
            old_is = vis[node];
            old_dc = vdc[node];
            old_ds = vds[node];
        }

        let new_c1 = (old_c1 + 1) % md;
        let new_ss = (old_ss + xm) % md;
        let new_ic = (old_ic + new_inc_count) % md;
        let new_is = (old_is + new_inc_sum) % md;
        let new_dc = (old_dc + new_dec_count) % md;
        let new_ds = (old_ds + new_dec_sum) % md;

        // Create the new leaf.
        let leaf_idx = vc1.len();
        left.push(0);
        right.push(0);
        vc1.push(new_c1);
        vss.push(new_ss);
        vic.push(new_ic);
        vis.push(new_is);
        vdc.push(new_dc);
        vds.push(new_ds);

        // Rebuild the path from the new leaf back to the new root.
        let mut child: usize = leaf_idx;
        let mut p: usize = path.len();
        while p > 0 {
            p = p - 1;
            let old_parent = path[p];
            let is_right = dirs[p];

            let mut old_left: usize = 0;
            let mut old_right: usize = 0;
            if old_parent != 0 {
                old_left = left[old_parent];
                old_right = right[old_parent];
            }

            let mut new_left: usize = old_left;
            let mut new_right: usize = old_right;
            if is_right {
                new_right = child;
            } else {
                new_left = child;
            }

            let new_node = vc1.len();
            left.push(new_left);
            right.push(new_right);
            vc1.push(0);
            vss.push(0);
            vic.push(0);
            vis.push(0);
            vdc.push(0);
            vds.push(0);

            child = new_node;
        }
        root = child;

        idx_nums += 1;
    }

    ans
}
