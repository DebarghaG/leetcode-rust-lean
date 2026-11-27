pub fn maximum_points(edges: &[Vec<i64>], coins: &[i64], k: i64) -> i64 {
    let n = coins.len();

    let mut head: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        head.push(-1);
        i += 1;
    }

    let mut to: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();
    let mut ec: i64 = 0;

    let mut ei = 0;
    while ei < edges.len() {
        let a = edges[ei][0];
        let b = edges[ei][1];
        let ai = a as usize;
        let bi = b as usize;

        to.push(b);
        next.push(head[ai]);
        head[ai] = ec;
        ec += 1;

        to.push(a);
        next.push(head[bi]);
        head[bi] = ec;
        ec += 1;

        ei += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut pi = 0;
    while pi < n {
        parent.push(-1);
        pi += 1;
    }
    parent[0] = -2;

    let mut order: Vec<i64> = Vec::new();
    order.push(0);

    let mut qi = 0;
    while qi < order.len() {
        let v = order[qi];
        qi += 1;
        let vv = v as usize;

        let mut e = head[vv];
        while e != -1 {
            let u = to[e as usize];
            if u != parent[vv] {
                parent[u as usize] = v;
                order.push(u);
            }
            e = next[e as usize];
        }
    }

    let hmax: usize = 16;
    let stride: usize = hmax + 1;
    let total: usize = n * stride;

    let mut dp: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < total {
        dp.push(0);
        z += 1;
    }

    let mut oi = order.len();
    while oi > 0 {
        oi -= 1;
        let v = order[oi];
        let vv = v as usize;
        let base = vv * stride;

        let mut cur = coins[vv];
        let mut h: usize = 0;

        while h < stride {
            let mut sum1: i64 = 0;
            let mut sum2: i64 = 0;

            let mut e = head[vv];
            while e != -1 {
                let u = to[e as usize];
                if u != parent[vv] {
                    let uu = u as usize;
                    let ubase = uu * stride;

                    sum1 += dp[ubase + h];

                    if h + 1 < stride {
                        sum2 += dp[ubase + h + 1];
                    } else {
                        sum2 += dp[ubase + h];
                    }
                }
                e = next[e as usize];
            }

            let gain1 = cur - k;
            let gain2 = cur / 2;

            let val1 = gain1 + sum1;
            let val2 = gain2 + sum2;

            if val1 > val2 {
                dp[base + h] = val1;
            } else {
                dp[base + h] = val2;
            }

            cur = cur / 2;
            h += 1;
        }
    }

    dp[0]
}
