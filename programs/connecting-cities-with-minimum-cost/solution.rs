pub fn minimum_cost(n: i64, connections: &[Vec<i64>]) -> i64 {
    if n <= 1 {
        return 0;
    }

    let m = connections.len();

    let mut xs: Vec<i64> = Vec::new();
    let mut ys: Vec<i64> = Vec::new();
    let mut cs: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < m {
        xs.push(connections[i][0]);
        ys.push(connections[i][1]);
        cs.push(connections[i][2]);
        i += 1;
    }

    let mut xs2: Vec<i64> = Vec::new();
    let mut ys2: Vec<i64> = Vec::new();
    let mut cs2: Vec<i64> = Vec::new();

    let mut t = 0usize;
    while t < m {
        xs2.push(0);
        ys2.push(0);
        cs2.push(0);
        t += 1;
    }

    let mut width = 1usize;
    while width < m {
        let mut start = 0usize;
        while start < m {
            let mut mid = start + width;
            if mid > m {
                mid = m;
            }

            let mut end = start + width + width;
            if end > m {
                end = m;
            }

            let mut l = start;
            let mut r = mid;
            let mut k = start;

            while l < mid && r < end {
                if cs[l] <= cs[r] {
                    xs2[k] = xs[l];
                    ys2[k] = ys[l];
                    cs2[k] = cs[l];
                    l += 1;
                } else {
                    xs2[k] = xs[r];
                    ys2[k] = ys[r];
                    cs2[k] = cs[r];
                    r += 1;
                }
                k += 1;
            }

            while l < mid {
                xs2[k] = xs[l];
                ys2[k] = ys[l];
                cs2[k] = cs[l];
                l += 1;
                k += 1;
            }

            while r < end {
                xs2[k] = xs[r];
                ys2[k] = ys[r];
                cs2[k] = cs[r];
                r += 1;
                k += 1;
            }

            start = end;
        }

        let mut j = 0usize;
        while j < m {
            xs[j] = xs2[j];
            ys[j] = ys2[j];
            cs[j] = cs2[j];
            j += 1;
        }

        width = width + width;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();

    let mut idx = 0i64;
    while idx <= n {
        parent.push(idx);
        size.push(1);
        idx += 1;
    }

    let mut total = 0i64;
    let mut used = 0i64;

    let mut e = 0usize;
    while e < m {
        let u = xs[e];
        let v = ys[e];
        let cost = cs[e];

        let mut ru = u;
        while parent[ru as usize] != ru {
            ru = parent[ru as usize];
        }

        let mut rv = v;
        while parent[rv as usize] != rv {
            rv = parent[rv as usize];
        }

        if ru != rv {
            let su = size[ru as usize];
            let sv = size[rv as usize];

            if su < sv {
                parent[ru as usize] = rv;
                size[rv as usize] = su + sv;
            } else {
                parent[rv as usize] = ru;
                size[ru as usize] = su + sv;
            }

            total += cost;
            used += 1;

            if used == n - 1 {
                return total;
            }
        }

        e += 1;
    }

    if used == n - 1 {
        total
    } else {
        -1
    }
}
