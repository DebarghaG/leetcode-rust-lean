const BASE: i64 = 200001;

// Insert `x` into ascending vector `h`, returning a fresh sorted vector.
fn insert_sorted(h: Vec<i64>, x: i64) -> Vec<i64> {
    let m: usize = h.len();
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut inserted: bool = false;
    while i < m {
        if !inserted && x < h[i] {
            out.push(x);
            inserted = true;
        }
        out.push(h[i]);
        i += 1;
    }
    if !inserted {
        out.push(x);
    }
    out
}

// Remove the smallest element (index 0) by rebuilding the vector.
fn pop_min(h: Vec<i64>) -> Vec<i64> {
    let m: usize = h.len();
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 1;
    while i < m {
        out.push(h[i]);
        i += 1;
    }
    out
}

pub fn total_cost(costs: &[i64], k: i64, candidates: i64) -> i64 {
    let n: usize = costs.len();
    if n == 0 || k <= 0 {
        return 0;
    }

    // c = min(candidates, n)
    let mut c: usize = 0;
    let mut t: i64 = 0;
    while t < candidates && c < n {
        c += 1;
        t += 1;
    }
    let l: usize = c;

    // r = max(c, n - c)
    let n_minus_c: usize = n - c;
    let mut r: usize = c;
    if n_minus_c > c {
        r = n_minus_c;
    }

    // Left pool: indices 0..l, encoded as cost*BASE + original_index.
    let mut left: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut idx: i64 = 0;
    while i < l {
        let x: i64 = costs[i] * BASE + idx;
        left = insert_sorted(left, x);
        i += 1;
        idx += 1;
    }

    // Right pool: indices r..n, encoded as cost*BASE + original_index.
    let mut right: Vec<i64> = Vec::new();
    let mut idx2: i64 = 0;
    let mut cnt: usize = 0;
    while cnt < r {
        idx2 += 1;
        cnt += 1;
    }
    // now idx2 == r (as i64)
    let mut j: usize = r;
    while j < n {
        let x: i64 = costs[j] * BASE + idx2;
        right = insert_sorted(right, x);
        j += 1;
        idx2 += 1;
    }

    // Refill pointers and matching i64 encoding indices.
    let mut left_next: usize = l;
    let mut left_idx: i64 = 0;
    let mut cnt2: usize = 0;
    while cnt2 < l {
        left_idx += 1;
        cnt2 += 1;
    }

    let mut right_next: usize = r - 1;
    let mut right_idx: i64 = 0;
    let mut cnt3: usize = 0;
    while cnt3 < r {
        right_idx += 1;
        cnt3 += 1;
    }
    right_idx -= 1; // r - 1

    let mut total: i64 = 0;
    let mut hired: i64 = 0;

    while hired < k {
        if left.len() == 0 && right.len() == 0 {
            break;
        }

        let mut take_left: bool = true;
        if left.len() == 0 {
            take_left = false;
        } else if right.len() != 0 && left[0] > right[0] {
            take_left = false;
        }

        if take_left {
            let val: i64 = left[0];
            total = total + val / BASE;
            left = pop_min(left);
            if left_next <= right_next {
                let x: i64 = costs[left_next] * BASE + left_idx;
                left = insert_sorted(left, x);
                left_next += 1;
                left_idx += 1;
            }
        } else {
            let val: i64 = right[0];
            total = total + val / BASE;
            right = pop_min(right);
            if right_next >= left_next {
                let x: i64 = costs[right_next] * BASE + right_idx;
                right = insert_sorted(right, x);
                right_next -= 1;
                right_idx -= 1;
            }
        }

        hired += 1;
    }

    total
}
