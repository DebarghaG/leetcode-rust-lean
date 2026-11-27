pub fn find_subtree_sizes(parent: &[i64], s: &[u8]) -> Vec<i64> {
    // Effective number of nodes: work with the shorter of the two inputs so we
    // never index out of bounds. For valid inputs both lengths are equal.
    let mut n = parent.len();
    if s.len() < n {
        n = s.len();
    }
    if n == 0 {
        return Vec::new();
    }

    // ---- Build children lists of the original tree (restricted to nodes < n) ----
    let mut children: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        children.push(Vec::new());
        i = i + 1;
    }
    i = 1;
    while i < n {
        let p = parent[i];
        if p >= 0 {
            let pu = p as usize;
            if pu < n {
                children[pu].push(i as i64);
            }
        }
        i = i + 1;
    }

    // rep[x] = closest proper ancestor of x with the same character (or -1).
    let mut rep: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        rep.push(-1);
        i = i + 1;
    }

    // old_seen[x] stores last_seen[c] before entering x, so we can restore on exit.
    let mut old_seen: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        old_seen.push(-1);
        i = i + 1;
    }

    let mut last_seen: Vec<i64> = Vec::new();
    i = 0;
    while i < 26 {
        last_seen.push(-1);
        i = i + 1;
    }

    let n64 = n as i64;

    // ---- DFS (explicit stack). Enter event for x is `x` (< n); exit is `n + x`. ----
    let mut stack: Vec<i64> = Vec::new();
    stack.push(0);
    let mut top: usize = 1;

    while top > 0 {
        top = top - 1;
        let ev = stack[top];

        if ev < n64 {
            let x = ev as usize;

            let mut c = (s[x] as i64) - 97;
            if c < 0 {
                c = 0;
            }
            if c > 25 {
                c = 25;
            }
            let ci = c as usize;

            let prev = last_seen[ci];
            old_seen[x] = prev;
            rep[x] = prev;
            last_seen[ci] = x as i64;

            let exit_ev = n64 + x as i64;
            if top < stack.len() {
                stack[top] = exit_ev;
            } else {
                stack.push(exit_ev);
            }
            top = top + 1;

            let mut j: usize = 0;
            while j < children[x].len() {
                let ch = children[x][j];
                if top < stack.len() {
                    stack[top] = ch;
                } else {
                    stack.push(ch);
                }
                top = top + 1;
                j = j + 1;
            }
        } else {
            let x = (ev - n64) as usize;

            let mut c = (s[x] as i64) - 97;
            if c < 0 {
                c = 0;
            }
            if c > 25 {
                c = 25;
            }
            let ci = c as usize;

            last_seen[ci] = old_seen[x];
        }
    }

    // ---- Compute new parent for each node ----
    let mut new_parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let r = rep[i];
        if r >= 0 {
            new_parent.push(r);
        } else {
            new_parent.push(parent[i]);
        }
        i = i + 1;
    }

    // ---- Build the final tree ----
    let mut fchildren: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        fchildren.push(Vec::new());
        i = i + 1;
    }
    i = 1;
    while i < n {
        let p = new_parent[i];
        if p >= 0 {
            let pu = p as usize;
            if pu < n {
                fchildren[pu].push(i as i64);
            }
        }
        i = i + 1;
    }

    // ---- Subtree sizes via post-order DFS ----
    let mut sizes: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        sizes.push(1);
        i = i + 1;
    }

    let mut stack2: Vec<i64> = Vec::new();
    stack2.push(0);
    let mut top2: usize = 1;

    while top2 > 0 {
        top2 = top2 - 1;
        let ev = stack2[top2];

        if ev < n64 {
            let x = ev as usize;

            let exit_ev = n64 + x as i64;
            if top2 < stack2.len() {
                stack2[top2] = exit_ev;
            } else {
                stack2.push(exit_ev);
            }
            top2 = top2 + 1;

            let mut j: usize = 0;
            while j < fchildren[x].len() {
                let ch = fchildren[x][j];
                if top2 < stack2.len() {
                    stack2[top2] = ch;
                } else {
                    stack2.push(ch);
                }
                top2 = top2 + 1;
                j = j + 1;
            }
        } else {
            let x = (ev - n64) as usize;
            let p = new_parent[x];
            if p >= 0 {
                let pu = p as usize;
                if pu < n {
                    sizes[pu] = sizes[pu] + sizes[x];
                }
            }
        }
    }

    sizes
}
