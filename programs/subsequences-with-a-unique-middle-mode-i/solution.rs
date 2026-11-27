fn comb2(x: i64) -> i64 {
    if x < 2 {
        0
    } else {
        x * (x - 1) / 2
    }
}

// Smallest index j with nums[j] == nums[i]. (Isolated simple search loop.)
fn find_first(nums: &[i64], i: usize) -> usize {
    let v: i64 = nums[i];
    let mut j: usize = 0;
    while j < i {
        if nums[j] == v {
            return j;
        }
        j += 1;
    }
    i
}

pub fn subsequences_with_middle_mode(nums: &[i64]) -> i64 {
    let modulo: i64 = 1000000007;
    let n: usize = nums.len();

    // Step 1: first occurrence index for every element (isolated vector build).
    let mut firstpos: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        firstpos.push(find_first(nums, i));
        i += 1;
    }

    // Step 2: prefix count of distinct values (single loop, tiny state).
    // cnt_before[t] = number of first occurrences among indices < t (length n+1).
    let mut cnt_before: Vec<usize> = Vec::new();
    let mut running: usize = 0;
    let mut i2: usize = 0;
    while i2 < n {
        cnt_before.push(running);
        if firstpos[i2] == i2 {
            running += 1;
        }
        i2 += 1;
    }
    cnt_before.push(running);
    let m: usize = running;

    // Step 3: contiguous group id per element (0..m-1, order of first appearance).
    let mut group: Vec<usize> = Vec::new();
    let mut i3: usize = 0;
    while i3 < n {
        group.push(cnt_before[firstpos[i3]]);
        i3 += 1;
    }

    // Step 4: frequency arrays on each side of the pivot, indexed by group id.
    let mut left: Vec<i64> = Vec::new();
    let mut right: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < m {
        left.push(0);
        right.push(0);
        t += 1;
    }
    t = 0;
    while t < n {
        let gid: usize = group[t];
        right[gid] = right[gid] + 1;
        t += 1;
    }

    // Step 5: sweep each possible middle index.
    let mut ans: i64 = 0;
    let mut kk: usize = 0;
    while kk < n {
        let xid: usize = group[kk];

        // Move the current element out of the right side.
        right[xid] = right[xid] - 1;

        let l_len: i64 = kk as i64;
        let r_len: i64 = (n - kk - 1) as i64;
        let lx: i64 = left[xid];
        let rx: i64 = right[xid];
        let m_left: i64 = l_len - lx;
        let m_right: i64 = r_len - rx;

        // Aggregate over ALL groups (unconditional accumulation), then remove
        // the pivot value's own contribution below.
        let mut s_left_all: i64 = 0;
        let mut s_right_all: i64 = 0;
        let mut cross_a_all: i64 = 0;
        let mut cross_b_all: i64 = 0;

        let mut y: usize = 0;
        while y < m {
            let ly: i64 = left[y];
            let ry: i64 = right[y];
            s_left_all += comb2(ly);
            s_right_all += comb2(ry);
            cross_a_all += ly * ry * (m_right - ry);
            cross_b_all += ly * ry * (m_left - ly);
            y += 1;
        }

        // Exclude the pivot value x itself.
        let s_left: i64 = s_left_all - comb2(lx);
        let s_right: i64 = s_right_all - comb2(rx);
        let cross_a: i64 = cross_a_all - lx * rx * (m_right - rx);
        let cross_b: i64 = cross_b_all - rx * lx * (m_left - lx);

        // Pairs of distinct non-x values within one side.
        let p_left: i64 = comb2(m_left) - s_left;
        let p_right: i64 = comb2(m_right) - s_right;

        // Pair choices classified by whether they contain x.
        let a0: i64 = comb2(m_left);
        let a1: i64 = lx * m_left;
        let b0: i64 = comb2(m_right);
        let b1: i64 = rx * m_right;

        let total_pairs: i64 = comb2(l_len) * comb2(r_len);

        // x appears at least 3 times total => always a unique mode.
        let high: i64 = total_pairs - a0 * b0 - a1 * b0 - a0 * b1;

        // x appears exactly twice total and the other three chosen values
        // are pairwise distinct => unique mode too.
        let good1: i64 = lx * (p_right * m_left - cross_a);
        let good2: i64 = rx * (p_left * m_right - cross_b);

        let valid_k: i64 = high + good1 + good2;
        ans = (ans + valid_k % modulo) % modulo;

        // The current element joins the left side for later middles.
        left[xid] = left[xid] + 1;

        kk += 1;
    }

    ans
}
