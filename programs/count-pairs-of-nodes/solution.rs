fn sort_i64_vec(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }

    let mut width: usize = 1;
    while width < n {
        let mut next: Vec<i64> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + width * 2;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    next.push(v[i]);
                    i += 1;
                } else {
                    next.push(v[j]);
                    j += 1;
                }
            }

            while i < mid {
                next.push(v[i]);
                i += 1;
            }

            while j < right {
                next.push(v[j]);
                j += 1;
            }

            left = right;
        }

        v = next;
        width = width * 2;
    }

    v
}

pub fn count_pairs(n: i64, edges: &[Vec<i64>], queries: &[i64]) -> Vec<i64> {
    let n_us = n as usize;

    let mut deg: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n_us {
        deg.push(0);
        i += 1;
    }

    let mut keys: Vec<i64> = Vec::new();
    let m_edges = edges.len();
    let mut e = 0;

    while e < m_edges {
        let mut u = edges[e][0] - 1;
        let mut v = edges[e][1] - 1;

        if u > v {
            let t = u;
            u = v;
            v = t;
        }

        let ui = u as usize;
        let vi = v as usize;

        deg[ui] += 1;
        deg[vi] += 1;

        let key = u * n + v;
        keys.push(key);

        e += 1;
    }

    let mut sorted_deg: Vec<i64> = Vec::new();
    let mut d = 0;
    while d < n_us {
        sorted_deg.push(deg[d]);
        d += 1;
    }

    let sorted_deg = sort_i64_vec(sorted_deg);
    let keys = sort_i64_vec(keys);
    let m = keys.len();

    let total_pairs: i64 = n * (n - 1) / 2;
    let mut answers: Vec<i64> = Vec::new();

    let mut qi = 0;
    while qi < queries.len() {
        let q = queries[qi];

        let mut r: usize = 0;
        if n_us > 0 {
            r = n_us - 1;
        }

        let mut less_or_equal: i64 = 0;
        let mut idx = 0;

        while idx < n_us {
            while r > idx && sorted_deg[idx] + sorted_deg[r] > q {
                r -= 1;
            }

            if r > idx {
                less_or_equal += (r - idx) as i64;
            }

            idx += 1;
        }

        let mut count = total_pairs - less_or_equal;

        let mut p = 0;
        while p < m {
            let key = keys[p];
            let mut j = p + 1;

            while j < m && keys[j] == key {
                j += 1;
            }

            let mult = (j - p) as i64;
            let a = key / n;
            let b = key % n;

            let ai = a as usize;
            let bi = b as usize;

            let sum_deg = deg[ai] + deg[bi];

            if sum_deg > q && sum_deg - mult <= q {
                count -= 1;
            }

            p = j;
        }

        answers.push(count);
        qi += 1;
    }

    answers
}
