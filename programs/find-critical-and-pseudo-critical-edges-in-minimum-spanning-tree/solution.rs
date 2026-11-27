fn mst_weight(n: i64, edges: &[Vec<i64>], order: &[i64], skip: i64, force: i64) -> i64 {
    let inf: i64 = 1_000_000_000;

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n {
        parent.push(i);
        size.push(1);
        i += 1;
    }

    let mut total: i64 = 0;
    let mut used: i64 = 0;

    let m: i64 = order.len() as i64;
    let steps: i64 = if force >= 0 { m + 1 } else { m };
    let mut step: i64 = 0;

    while step < steps {
        let mut idx: i64 = -1;
        let mut do_edge: bool = true;

        if force >= 0 && step == 0 {
            idx = force;
        } else {
            let pos: i64 = if force >= 0 { step - 1 } else { step };
            idx = order[pos as usize];

            if idx == skip {
                do_edge = false;
            }
            if force >= 0 && idx == force {
                do_edge = false;
            }
        }

        if do_edge {
            let e = &edges[idx as usize];
            let a = e[0];
            let b = e[1];

            let mut ra = a;
            while parent[ra as usize] != ra {
                ra = parent[ra as usize];
            }

            let mut rb = b;
            while parent[rb as usize] != rb {
                rb = parent[rb as usize];
            }

            if ra != rb {
                let sa = size[ra as usize];
                let sb = size[rb as usize];

                if sa < sb {
                    parent[ra as usize] = rb;
                    size[rb as usize] = sb + sa;
                } else {
                    parent[rb as usize] = ra;
                    size[ra as usize] = sa + sb;
                }

                total += e[2];
                used += 1;
            }
        }

        step += 1;
    }

    if used == n - 1 {
        total
    } else {
        inf
    }
}

pub fn find_critical_and_pseudo_critical_edges(n: i64, edges: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = edges.len();

    let mut order: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < m {
        order.push(i as i64);
        i += 1;
    }

    let mut a = 1usize;
    while a < m {
        let key = order[a];
        let key_w = edges[key as usize][2];
        let mut b = a;

        while b > 0 && edges[order[b - 1] as usize][2] > key_w {
            order[b] = order[b - 1];
            b -= 1;
        }

        order[b] = key;
        a += 1;
    }

    let original = mst_weight(n, edges, &order, -1, -1);

    let mut critical: Vec<i64> = Vec::new();
    let mut pseudo: Vec<i64> = Vec::new();

    let mut k = 0usize;
    while k < m {
        let idx = order[k];

        let without = mst_weight(n, edges, &order, idx, -1);

        if without >= 1_000_000_000 || without > original {
            critical.push(idx);
        } else {
            let with_edge = mst_weight(n, edges, &order, -1, idx);
            if with_edge == original {
                pseudo.push(idx);
            }
        }

        k += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    out.push(critical);
    out.push(pseudo);
    out
}
