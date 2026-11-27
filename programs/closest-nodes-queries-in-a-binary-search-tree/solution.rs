fn inorder(t: &Tree, out: Vec<i64>) -> Vec<i64> {
    match t {
        Tree::Null => out,
        Tree::Node(v, l, r) => {
            let mut out = inorder(&**l, out);
            out.push(*v);
            inorder(&**r, out)
        }
    }
}

pub fn closest_nodes(root: &Tree, queries: &[i64]) -> Vec<Vec<i64>> {
    let vals = inorder(root, Vec::new());
    let m = vals.len();
    let n = queries.len();

    let mut ans: Vec<Vec<i64>> = Vec::new();
    let mut i = 0usize;

    while i < n {
        let q = queries[i];

        // Smallest value >= q.
        let mut lo = 0usize;
        let mut hi = m;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if vals[mid] < q {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let min_ge = if lo < m { vals[lo] } else { -1 };

        // Largest value <= q.
        let mut lo2 = 0usize;
        let mut hi2 = m;
        while lo2 < hi2 {
            let mid = lo2 + (hi2 - lo2) / 2;
            if vals[mid] <= q {
                lo2 = mid + 1;
            } else {
                hi2 = mid;
            }
        }
        let max_le = if lo2 > 0 { vals[lo2 - 1] } else { -1 };

        let mut row: Vec<i64> = Vec::new();
        row.push(max_le);
        row.push(min_ge);
        ans.push(row);

        i = i + 1;
    }

    ans
}
