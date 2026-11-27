pub fn longest_path(parent: &[i64], s: &[u8]) -> i64 {
    let n = parent.len();
    if n == 0 {
        return 0;
    }

    let mut head: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        head.push(-1);
        next.push(-1);
        i = i + 1;
    }

    i = 1;
    while i < n {
        let p = parent[i];
        if p >= 0 {
            let pi = p as usize;
            next[i] = head[pi];
            head[pi] = i as i64;
        }
        i = i + 1;
    }

    let mut stack: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        stack.push(0);
        i = i + 1;
    }

    let mut sp: usize = 0;
    stack[sp] = 0;
    sp = sp + 1;

    let mut order: Vec<i64> = Vec::new();
    while sp > 0 {
        sp = sp - 1;
        let u = stack[sp];
        order.push(u);

        let mut child = head[u as usize];
        while child != -1 {
            stack[sp] = child;
            sp = sp + 1;
            child = next[child as usize];
        }
    }

    let mut down: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        down.push(1);
        i = i + 1;
    }

    let mut ans: i64 = 1;
    let mut k = order.len();
    while k > 0 {
        k = k - 1;
        let u = order[k];
        let ui = u as usize;

        let mut best: i64 = 0;
        let mut second: i64 = 0;
        let mut child = head[ui];

        while child != -1 {
            let vi = child as usize;
            if s[ui] != s[vi] {
                let cand = down[vi];
                if cand > best {
                    second = best;
                    best = cand;
                } else if cand > second {
                    second = cand;
                }
            }
            child = next[vi];
        }

        down[ui] = best + 1;
        let through = 1 + best + second;
        if through > ans {
            ans = through;
        }
    }

    ans
}
