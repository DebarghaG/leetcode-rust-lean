fn collect(
    t: &Tree,
    row: i64,
    col: i64,
    cols: &mut Vec<i64>,
    rows: &mut Vec<i64>,
    vals: &mut Vec<i64>,
) {
    match t {
        Tree::Null => {}
        Tree::Node(v, l, r) => {
            cols.push(col);
            rows.push(row);
            vals.push(*v);
            collect(&**l, row + 1, col - 1, cols, rows, vals);
            collect(&**r, row + 1, col + 1, cols, rows, vals);
        }
    }
}

pub fn vertical_traversal(root: &Tree) -> Vec<Vec<i64>> {
    let mut cols: Vec<i64> = Vec::new();
    let mut rows: Vec<i64> = Vec::new();
    let mut vals: Vec<i64> = Vec::new();

    collect(root, 0, 0, &mut cols, &mut rows, &mut vals);

    let n = cols.len();

    let mut i: usize = 1;
    while i < n {
        let c = cols[i];
        let r = rows[i];
        let v = vals[i];

        let mut j = i;
        let mut go = true;
        while j > 0 && go {
            let pc = cols[j - 1];
            let pr = rows[j - 1];
            let pv = vals[j - 1];

            let mut greater = false;
            if pc > c {
                greater = true;
            } else if pc == c {
                if pr > r {
                    greater = true;
                } else if pr == r {
                    if pv > v {
                        greater = true;
                    }
                }
            }

            if greater {
                cols[j] = pc;
                rows[j] = pr;
                vals[j] = pv;
                j = j - 1;
            } else {
                go = false;
            }
        }

        cols[j] = c;
        rows[j] = r;
        vals[j] = v;
        i = i + 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    if n == 0 {
        return out;
    }

    let mut start: usize = 0;
    while start < n {
        let mut end = start + 1;
        while end < n && cols[end] == cols[start] {
            end = end + 1;
        }

        let mut group: Vec<i64> = Vec::new();
        let mut k = start;
        while k < end {
            group.push(vals[k]);
            k = k + 1;
        }

        out.push(group);
        start = end;
    }

    out
}
