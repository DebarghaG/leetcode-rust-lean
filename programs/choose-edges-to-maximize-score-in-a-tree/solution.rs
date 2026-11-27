pub fn max_score(edges: &[Vec<i64>]) -> i64 {
    let n = edges.len();
    if n == 0 {
        return 0;
    }

    let mut first: Vec<usize> = Vec::new();
    let mut next: Vec<usize> = Vec::new();
    let mut weight: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        first.push(n);
        next.push(n);
        weight.push(0);
        i += 1;
    }

    let mut v: usize = 1;
    while v < n {
        let p = edges[v][0];
        let w = edges[v][1];
        weight[v] = w;

        if p >= 0 {
            let pu = p as usize;
            if pu < n {
                next[v] = first[pu];
                first[pu] = v;
            }
        }

        v += 1;
    }

    let mut order: Vec<usize> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    stack.push(0);
    let mut top: usize = 1;

    while top > 0 {
        top -= 1;
        let u = stack[top];
        order.push(u);

        let mut c = first[u];
        while c < n {
            if top == stack.len() {
                stack.push(c);
            } else {
                stack[top] = c;
            }
            top += 1;
            c = next[c];
        }
    }

    let mut dp0: Vec<i64> = Vec::new();
    let mut dp1: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        dp0.push(0);
        dp1.push(0);
        i += 1;
    }

    let mut idx: usize = order.len();
    while idx > 0 {
        idx -= 1;
        let u = order[idx];

        let mut sum0: i64 = 0;
        let mut best_gain: i64 = 0;

        let mut c = first[u];
        while c < n {
            sum0 += dp0[c];

            let gain = weight[c] + dp1[c] - dp0[c];
            if gain > best_gain {
                best_gain = gain;
            }

            c = next[c];
        }

        dp1[u] = sum0;
        dp0[u] = sum0 + best_gain;
    }

    dp0[0]
}
