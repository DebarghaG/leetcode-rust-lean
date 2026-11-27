pub fn sum_of_good_subsequences(nums: &[i64]) -> i64 {
    const MOD: i64 = 1_000_000_007;

    let n = nums.len();
    if n == 0 {
        return 0;
    }

    // Copy nums into an owned vector.
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    // Bottom-up merge sort, avoiding in-place indexed assignment.
    let mut width: usize = 1;
    while width < n {
        let mut out: Vec<i64> = Vec::new();
        let mut start: usize = 0;
        while start < n {
            let mid = if start + width < n { start + width } else { n };
            let end = if start + width * 2 < n { start + width * 2 } else { n };

            let mut a: usize = start;
            let mut b: usize = mid;

            while a < mid && b < end {
                if v[a] <= v[b] {
                    out.push(v[a]);
                    a += 1;
                } else {
                    out.push(v[b]);
                    b += 1;
                }
            }
            while a < mid {
                out.push(v[a]);
                a += 1;
            }
            while b < end {
                out.push(v[b]);
                b += 1;
            }

            start = end;
        }
        v = out;
        width = width * 2;
    }

    // Build sorted unique values.
    let mut vals: Vec<i64> = Vec::new();
    let mut first: bool = true;
    let mut last: i64 = 0;

    i = 0;
    while i < n {
        if first || v[i] != last {
            vals.push(v[i]);
            last = v[i];
            first = false;
        }
        i += 1;
    }

    let m = vals.len();
    if m == 0 {
        return 0;
    }

    // Persistent segment tree. Node 0 is the empty/null node.
    let mut lc: Vec<usize> = Vec::new();
    let mut rc: Vec<usize> = Vec::new();
    let mut cnt: Vec<i64> = Vec::new();
    let mut sum: Vec<i64> = Vec::new();

    lc.push(0);
    rc.push(0);
    cnt.push(0);
    sum.push(0);

    let mut root: usize = 0;
    let mut answer: i64 = 0;

    i = 0;
    while i < n {
        let x = nums[i];

        // Find position of x.
        let mut lo: usize = 0;
        let mut hi: usize = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if vals[mid] < x {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let pos_x = lo;

        // Find position of x - 1.
        let target_lo = x - 1;
        lo = 0;
        hi = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if vals[mid] < target_lo {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let pos_lo = if lo < m && vals[lo] == target_lo { lo } else { m };

        // Find position of x + 1.
        let target_hi = x + 1;
        lo = 0;
        hi = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if vals[mid] < target_hi {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let pos_hi = if lo < m && vals[lo] == target_hi { lo } else { m };

        // Query x - 1.
        let mut c_lo: i64 = 0;
        let mut s_lo: i64 = 0;
        if pos_lo < m {
            let mut node = root;
            let mut l: usize = 0;
            let mut r: usize = m - 1;

            while l < r {
                let mid = l + (r - l) / 2;
                if pos_lo <= mid {
                    if node >= lc.len() {
                        node = 0;
                    }
                    node = lc[node];
                    r = mid;
                } else {
                    if node >= rc.len() {
                        node = 0;
                    }
                    node = rc[node];
                    l = mid + 1;
                }
            }

            if node >= cnt.len() {
                node = 0;
            }
            if node >= sum.len() {
                node = 0;
            }
            c_lo = cnt[node];
            s_lo = sum[node];
        }

        // Query x + 1.
        let mut c_hi: i64 = 0;
        let mut s_hi: i64 = 0;
        if pos_hi < m {
            let mut node = root;
            let mut l: usize = 0;
            let mut r: usize = m - 1;

            while l < r {
                let mid = l + (r - l) / 2;
                if pos_hi <= mid {
                    if node >= lc.len() {
                        node = 0;
                    }
                    node = lc[node];
                    r = mid;
                } else {
                    if node >= rc.len() {
                        node = 0;
                    }
                    node = rc[node];
                    l = mid + 1;
                }
            }

            if node >= cnt.len() {
                node = 0;
            }
            if node >= sum.len() {
                node = 0;
            }
            c_hi = cnt[node];
            s_hi = sum[node];
        }

        let mut new_count = 1 + c_lo;
        new_count = (new_count + c_hi) % MOD;

        let xm = x % MOD;
        let mut new_total = xm;
        new_total = (new_total + s_lo) % MOD;
        new_total = (new_total + (c_lo * xm) % MOD) % MOD;
        new_total = (new_total + s_hi) % MOD;
        new_total = (new_total + (c_hi * xm) % MOD) % MOD;

        answer = (answer + new_total) % MOD;

        // Persistent point update at pos_x.
        let mut path_nodes: Vec<usize> = Vec::new();
        let mut path_dirs: Vec<i64> = Vec::new();

        let mut l: usize = 0;
        let mut r: usize = m - 1;
        let mut node = root;

        while l < r {
            path_nodes.push(node);

            let mid = l + (r - l) / 2;
            if pos_x <= mid {
                path_dirs.push(1);
                if node >= lc.len() {
                    node = 0;
                }
                node = lc[node];
                r = mid;
            } else {
                path_dirs.push(0);
                if node >= rc.len() {
                    node = 0;
                }
                node = rc[node];
                l = mid + 1;
            }
        }

        if node >= cnt.len() {
            node = 0;
        }
        if node >= sum.len() {
            node = 0;
        }

        let old_c = cnt[node];
        let old_s = sum[node];

        let mut new_child: usize = lc.len();
        lc.push(0);
        rc.push(0);
        cnt.push((old_c + new_count) % MOD);
        sum.push((old_s + new_total) % MOD);

        let depth = path_nodes.len();
        let mut k: usize = depth;

        while k > 0 {
            k -= 1;

            let mut old: usize = 0;
            if k < path_nodes.len() {
                old = path_nodes[k];
            } else {
                old = 0;
            }

            let mut dir: i64 = 0;
            if k < path_dirs.len() {
                dir = path_dirs[k];
            } else {
                dir = 0;
            }

            if old >= lc.len() {
                old = 0;
            }
            if old >= rc.len() {
                old = 0;
            }
            if old >= cnt.len() {
                old = 0;
            }
            if old >= sum.len() {
                old = 0;
            }

            let new_idx = lc.len();

            if dir == 1 {
                let mut right_child: usize = 0;
                if old < rc.len() {
                    right_child = rc[old];
                } else {
                    right_child = 0;
                }
                lc.push(new_child);
                rc.push(right_child);
            } else {
                let mut left_child: usize = 0;
                if old < lc.len() {
                    left_child = lc[old];
                } else {
                    left_child = 0;
                }
                lc.push(left_child);
                rc.push(new_child);
            }

            let mut old_cnt: i64 = 0;
            if old < cnt.len() {
                old_cnt = cnt[old];
            } else {
                old_cnt = 0;
            }

            let mut old_sum: i64 = 0;
            if old < sum.len() {
                old_sum = sum[old];
            } else {
                old_sum = 0;
            }

            cnt.push((old_cnt + new_count) % MOD);
            sum.push((old_sum + new_total) % MOD);

            new_child = new_idx;
        }

        root = new_child;
        i += 1;
    }

    answer
}
