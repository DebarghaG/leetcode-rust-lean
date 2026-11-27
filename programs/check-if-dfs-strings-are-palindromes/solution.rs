fn index_of(values: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = values.len();
    while lo < hi {
        let mid = (lo + hi) / 2;
        if values[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn find_answer(parent: &[i64], s: &[u8]) -> Vec<bool> {
    let mut n = parent.len();
    if s.len() < n {
        n = s.len();
    }

    let mut ans: Vec<bool> = Vec::new();
    if n == 0 {
        return ans;
    }

    // ident[k] = k as an i64 value.  This lets us convert nonnegative i64
    // node ids to usize indices without using `as` casts.
    let mut ident: Vec<i64> = Vec::new();
    let mut k_i: i64 = 0;
    let mut k_u: usize = 0;
    while k_u < n {
        ident.push(k_i);
        k_i += 1;
        k_u += 1;
    }

    // children[p] contains the children of p, in increasing order.
    let mut children: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        children.push(row);
        i += 1;
    }

    i = 1;
    while i < n {
        let p_val = parent[i];
        let p = index_of(&ident, p_val);
        let child_i64 = ident[i];
        children[p].push(child_i64);
        i += 1;
    }

    // For each node, record its postorder interval [left, right].
    let mut lefts: Vec<Vec<i64>> = Vec::new();
    let mut rights: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let row_l: Vec<i64> = Vec::new();
        let row_r: Vec<i64> = Vec::new();
        lefts.push(row_l);
        rights.push(row_r);
        i += 1;
    }

    let mut post: Vec<u8> = Vec::new();
    let mut post_len: i64 = 0;

    let mut stack_node: Vec<usize> = Vec::new();
    let mut stack_next: Vec<usize> = Vec::new();
    let mut stack_start: Vec<i64> = Vec::new();

    stack_node.push(0);
    stack_next.push(0);
    stack_start.push(0);

    while stack_node.len() > 0 {
        let top = stack_node.len() - 1;
        let x = stack_node[top];
        let idx = stack_next[top];

        if idx < children[x].len() {
            let y_i64 = children[x][idx];
            let y = index_of(&ident, y_i64);
            let st = stack_start[top];

            stack_node.pop();
            stack_next.pop();
            stack_start.pop();

            stack_node.push(x);
            stack_next.push(idx + 1);
            stack_start.push(st);

            stack_node.push(y);
            stack_next.push(0);
            stack_start.push(post_len);
        } else {
            let l = stack_start[top];
            let ch = s[x];
            post.push(ch);
            let r = post_len;
            post_len += 1;

            lefts[x].push(l);
            rights[x].push(r);

            stack_node.pop();
            stack_next.pop();
            stack_start.pop();
        }
    }

    let m = post.len();

    // Odd-length Manacher radii.
    let mut d1: Vec<usize> = Vec::new();
    let mut l: usize = 0;
    let mut r: usize = 0; // exclusive
    let mut c: usize = 0;
    while c < m {
        let mut rad: usize;
        if c < r {
            let mirror = l + r - c - 1;
            let a = d1[mirror];
            let b = r - c;
            if a < b {
                rad = a;
            } else {
                rad = b;
            }
        } else {
            rad = 1;
        }

        while c >= rad && c + rad < m && post[c - rad] == post[c + rad] {
            rad += 1;
        }

        d1.push(rad);

        if c + rad > r {
            l = c + 1 - rad;
            r = c + rad;
        }
        c += 1;
    }

    // Even-length Manacher radii.
    let mut d2: Vec<usize> = Vec::new();
    l = 0;
    r = 0;
    c = 0;
    while c < m {
        let mut rad: usize;
        if c < r {
            let mirror = l + r - c;
            let a = d2[mirror];
            let b = r - c;
            if a < b {
                rad = a;
            } else {
                rad = b;
            }
        } else {
            rad = 0;
        }

        while c > rad && c + rad < m && post[c - rad - 1] == post[c + rad] {
            rad += 1;
        }

        d2.push(rad);

        if c + rad > r {
            l = c - rad;
            r = c + rad;
        }
        c += 1;
    }

    i = 0;
    while i < n {
        let a = lefts[i][0];
        let b = rights[i][0];
        let left = index_of(&ident, a);
        let right = index_of(&ident, b);
        let len = right - left + 1;

        let mut ok = false;
        if len % 2 == 1 {
            let center = (left + right) / 2;
            let need = (len + 1) / 2;
            if d1[center] >= need {
                ok = true;
            }
        } else {
            let center = (left + right + 1) / 2;
            let need = len / 2;
            if d2[center] >= need {
                ok = true;
            }
        }

        ans.push(ok);
        i += 1;
    }

    ans
}
