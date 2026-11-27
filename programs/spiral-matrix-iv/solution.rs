fn collect_rev(l: &List) -> Vec<i64> {
    match l {
        List::Nil => Vec::new(),
        List::Cons(v, next) => {
            let mut r: Vec<i64> = collect_rev(&**next);
            r.push(*v);
            r
        }
    }
}

pub fn spiral_matrix(m: i64, n: i64, head: &List) -> Vec<Vec<i64>> {
    let rows: usize = m as usize;
    let cols: usize = n as usize;
    let total: usize = rows * cols;

    // Collect list values into a Vec (comes out reversed), then reverse in place.
    let mut vals: Vec<i64> = collect_rev(head);
    let vlen: usize = vals.len();
    let mut a: usize = 0;
    let mut b: usize = vlen;
    while a + 1 < b {
        b -= 1;
        let tmp: i64 = vals[a];
        vals[a] = vals[b];
        vals[b] = tmp;
        a += 1;
    }

    // Flat output buffer, prefilled with -1.
    let mut flat: Vec<i64> = Vec::new();
    let mut fi: usize = 0;
    while fi < total {
        flat.push(-1);
        fi += 1;
    }

    let len: usize = vals.len();
    let mut k: usize = 0;
    let mut top: i64 = 0;
    let mut bottom: i64 = rows as i64 - 1;
    let mut left: i64 = 0;
    let mut right: i64 = cols as i64 - 1;

    while k < len && top <= bottom && left <= right {
        // Left -> right along top row.
        let mut c: i64 = left;
        while c <= right && k < len {
            flat[(top as usize) * cols + (c as usize)] = vals[k];
            k += 1;
            c += 1;
        }
        top += 1;

        // Top -> bottom along right column.
        let mut r: i64 = top;
        while r <= bottom && k < len {
            flat[(r as usize) * cols + (right as usize)] = vals[k];
            k += 1;
            r += 1;
        }
        right -= 1;

        // Right -> left along bottom row.
        let mut c2: i64 = right;
        while c2 >= left && k < len {
            flat[(bottom as usize) * cols + (c2 as usize)] = vals[k];
            k += 1;
            c2 -= 1;
        }
        bottom -= 1;

        // Bottom -> top along left column.
        let mut r2: i64 = bottom;
        while r2 >= top && k < len {
            flat[(r2 as usize) * cols + (left as usize)] = vals[k];
            k += 1;
            r2 -= 1;
        }
        left += 1;
    }

    // Reshape flat buffer into the 2-D output.
    let mut out: Vec<Vec<i64>> = Vec::new();
    let mut ri: usize = 0;
    while ri < rows {
        let mut row: Vec<i64> = Vec::new();
        let mut ci: usize = 0;
        while ci < cols {
            row.push(flat[ri * cols + ci]);
            ci += 1;
        }
        out.push(row);
        ri += 1;
    }

    out
}
