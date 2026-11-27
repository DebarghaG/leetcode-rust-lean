pub fn placed_coins(edges: &[Vec<i64>], cost: &[i64]) -> Vec<i64> {
    let n = cost.len();

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    let m = edges.len();
    let mut e: usize = 0;
    while e < m {
        let a = edges[e][0];
        let b = edges[e][1];
        let au = a as usize;
        let bu = b as usize;
        adj[au].push(b);
        adj[bu].push(a);
        e += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        parent.push(-2);
        i += 1;
    }
    parent[0] = -1;

    let mut order: Vec<i64> = Vec::new();
    let mut stack: Vec<i64> = Vec::new();
    stack.push(0);
    let mut sp: usize = 1;

    while sp > 0 {
        sp -= 1;
        let u = stack[sp];
        order.push(u);

        let ui = u as usize;
        let mut j: usize = 0;
        while j < adj[ui].len() {
            let v = adj[ui][j];
            let vi = v as usize;
            if v != parent[ui] && parent[vi] == -2 {
                parent[vi] = u;
                if sp < stack.len() {
                    stack[sp] = v;
                } else {
                    stack.push(v);
                }
                sp += 1;
            }
            j += 1;
        }
    }

    let mut coins: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        coins.push(1);
        i += 1;
    }

    let mut size: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        size.push(1);
        i += 1;
    }

    // Each summary row stores:
    // [largest, second largest, third largest, smallest, second smallest]
    let mut summary: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let mut row: Vec<i64> = Vec::new();
        row.push(0);
        row.push(0);
        row.push(0);
        row.push(0);
        row.push(0);
        summary.push(row);
        i += 1;
    }

    let neg: i64 = -1000000000000000000;
    let pos: i64 = 1000000000000000000;

    let mut oi: usize = order.len();
    while oi > 0 {
        oi -= 1;
        let u = order[oi];
        let ui = u as usize;

        let mut top1: i64 = neg;
        let mut top2: i64 = neg;
        let mut top3: i64 = neg;
        let mut min1: i64 = pos;
        let mut min2: i64 = pos;

        let mut sz: i64 = 1;
        let own = cost[ui];

        if own > top1 {
            top3 = top2;
            top2 = top1;
            top1 = own;
        } else if own > top2 {
            top3 = top2;
            top2 = own;
        } else if own > top3 {
            top3 = own;
        }

        if own < min1 {
            min2 = min1;
            min1 = own;
        } else if own < min2 {
            min2 = own;
        }

        let mut j: usize = 0;
        while j < adj[ui].len() {
            let v = adj[ui][j];
            let vi = v as usize;

            if parent[vi] == u {
                sz += size[vi];

                let mut k: usize = 0;
                while k < 3 {
                    let x = summary[vi][k];
                    if x > top1 {
                        top3 = top2;
                        top2 = top1;
                        top1 = x;
                    } else if x > top2 {
                        top3 = top2;
                        top2 = x;
                    } else if x > top3 {
                        top3 = x;
                    }
                    k += 1;
                }

                let mut k2: usize = 3;
                while k2 < 5 {
                    let x = summary[vi][k2];
                    if x < min1 {
                        min2 = min1;
                        min1 = x;
                    } else if x < min2 {
                        min2 = x;
                    }
                    k2 += 1;
                }
            }

            j += 1;
        }

        size[ui] = sz;
        summary[ui][0] = top1;
        summary[ui][1] = top2;
        summary[ui][2] = top3;
        summary[ui][3] = min1;
        summary[ui][4] = min2;

        if sz < 3 {
            coins[ui] = 1;
        } else {
            let p1 = top1 * top2 * top3;
            let p2 = min1 * min2 * top1;
            let mut ans = p1;
            if p2 > ans {
                ans = p2;
            }
            if ans < 0 {
                ans = 0;
            }
            coins[ui] = ans;
        }
    }

    coins
}
