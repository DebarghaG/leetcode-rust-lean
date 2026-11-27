fn merge_sort(mut src: Vec<i64>) -> Vec<i64> {
    let n = src.len();
    let mut width: usize = 1;
    while width < n {
        let mut dst: Vec<i64> = Vec::new();
        let mut start: usize = 0;
        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }
            let mut end = start + width * 2;
            if end > n {
                end = n;
            }
            let mut i = start;
            let mut j = mid;
            while i < mid && j < end {
                if src[i] <= src[j] {
                    dst.push(src[i]);
                    i += 1;
                } else {
                    dst.push(src[j]);
                    j += 1;
                }
            }
            while i < mid {
                dst.push(src[i]);
                i += 1;
            }
            while j < end {
                dst.push(src[j]);
                j += 1;
            }
            start = end;
        }
        src = dst;
        width = width * 2;
    }
    src
}

fn insert(
    lc: &mut Vec<usize>,
    rc: &mut Vec<usize>,
    cnt: &mut Vec<i64>,
    sm: &mut Vec<i64>,
    root: usize,
    p: usize,
    m: usize,
    val: i64,
) -> usize {
    let mut path_nodes: Vec<usize> = Vec::new();
    let mut dirs: Vec<u8> = Vec::new();
    let mut cur = root;
    let mut lo: usize = 0;
    let mut hi: usize = m;
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        path_nodes.push(cur);
        if p < mid {
            dirs.push(0);
            cur = lc[cur];
            hi = mid;
        } else {
            dirs.push(1);
            cur = rc[cur];
            lo = mid;
        }
    }
    let leaf_cnt = cnt[cur] + 1;
    let leaf_sum = sm[cur] + val;
    let leaf_index = lc.len();
    lc.push(0);
    rc.push(0);
    cnt.push(leaf_cnt);
    sm.push(leaf_sum);
    let mut new_child = leaf_index;
    let mut t = path_nodes.len();
    while t > 0 {
        t -= 1;
        let old = path_nodes[t];
        let dir = dirs[t];
        let new_lc = if dir == 0 { new_child } else { lc[old] };
        let new_rc = if dir == 0 { rc[old] } else { new_child };
        let new_cnt = cnt[old] + 1;
        let new_sum = sm[old] + val;
        let parent_index = lc.len();
        lc.push(new_lc);
        rc.push(new_rc);
        cnt.push(new_cnt);
        sm.push(new_sum);
        new_child = parent_index;
    }
    new_child
}

pub fn min_operations(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut k_usize: usize = 0;
    let mut k_counter: i64 = 0;
    while k_counter < k {
        k_usize += 1;
        k_counter += 1;
    }

    let mut src: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        src.push(nums[i]);
        i += 1;
    }
    let sorted = merge_sort(src);

    let mut uniq: Vec<i64> = Vec::new();
    i = 0;
    while i < sorted.len() {
        if i == 0 || sorted[i] != sorted[i - 1] {
            uniq.push(sorted[i]);
        }
        i += 1;
    }
    let m = uniq.len();

    let mut lc: Vec<usize> = Vec::new();
    let mut rc: Vec<usize> = Vec::new();
    let mut cnt: Vec<i64> = Vec::new();
    let mut sm: Vec<i64> = Vec::new();
    lc.push(0);
    rc.push(0);
    cnt.push(0);
    sm.push(0);

    let mut roots: Vec<usize> = Vec::new();
    roots.push(0);

    let mut ans: i64 = 1000000000000000000;
    let mut window_sum: i64 = 0;

    i = 0;
    while i < n {
        let val = nums[i];
        let mut lo: usize = 0;
        let mut hi: usize = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if uniq[mid] < val {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let p = lo;
        let old_root = roots[i];
        let new_root = insert(&mut lc, &mut rc, &mut cnt, &mut sm, old_root, p, m, val);
        roots.push(new_root);

        window_sum += val;
        if i >= k_usize {
            window_sum -= nums[i - k_usize];
        }

        if i + 1 >= k_usize {
            let l = i + 1 - k_usize;
            let mut rr = roots[i + 1];
            let mut rl = roots[l];
            let mut qlo: usize = 0;
            let mut qhi: usize = m;
            let mut rem = (k + 1) / 2;
            let mut cnt_left: i64 = 0;
            let mut sum_left: i64 = 0;
            while qhi - qlo > 1 {
                let mid = qlo + (qhi - qlo) / 2;
                let left_r = lc[rr];
                let left_l = lc[rl];
                let c = cnt[left_r] - cnt[left_l];
                if rem <= c {
                    rr = left_r;
                    rl = left_l;
                    qhi = mid;
                } else {
                    rem -= c;
                    cnt_left += c;
                    sum_left += sm[left_r] - sm[left_l];
                    rr = rc[rr];
                    rl = rc[rl];
                    qlo = mid;
                }
            }
            let med = uniq[qlo];
            let cost = med * cnt_left - sum_left
                + (window_sum - sum_left)
                - med * (k - cnt_left);
            if cost < ans {
                ans = cost;
            }
        }

        i += 1;
    }

    ans
}
