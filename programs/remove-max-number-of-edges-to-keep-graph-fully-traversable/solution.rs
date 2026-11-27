fn make_parent(n: i64) -> Vec<i64> {
    let mut parent: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i <= n {
        parent.push(i);
        i += 1;
    }
    parent
}

fn make_rank(n: i64) -> Vec<i64> {
    let mut rank: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i <= n {
        rank.push(0);
        i += 1;
    }
    rank
}

fn dsu_find(parent: &mut Vec<i64>, x: i64) -> i64 {
    let mut cur = x;
    while parent[cur as usize] != cur {
        let p = parent[cur as usize];
        let gp = parent[p as usize];
        parent[cur as usize] = gp;
        cur = gp;
    }
    cur
}

fn dsu_union(parent: &mut Vec<i64>, rank: &mut Vec<i64>, x: i64, y: i64) -> bool {
    let rx = dsu_find(parent, x);
    let ry = dsu_find(parent, y);

    if rx == ry {
        return false;
    }

    let rxu = rx as usize;
    let ryu = ry as usize;

    if rank[rxu] < rank[ryu] {
        parent[rxu] = ry;
    } else if rank[rxu] > rank[ryu] {
        parent[ryu] = rx;
    } else {
        parent[ryu] = rx;
        rank[rxu] = rank[rxu] + 1;
    }

    true
}

pub fn max_num_edges_to_remove(n: i64, edges: &[Vec<i64>]) -> i64 {
    let m = edges.len();

    let mut parent_a = make_parent(n);
    let mut parent_b = make_parent(n);
    let mut rank_a = make_rank(n);
    let mut rank_b = make_rank(n);

    let mut comp_a = n;
    let mut comp_b = n;
    let mut removed: i64 = 0;

    let mut i: usize = 0;
    while i < m {
        if edges[i][0] == 3 {
            let u = edges[i][1];
            let v = edges[i][2];

            let ua = dsu_union(&mut parent_a, &mut rank_a, u, v);
            let ub = dsu_union(&mut parent_b, &mut rank_b, u, v);

            if ua {
                comp_a -= 1;
            }
            if ub {
                comp_b -= 1;
            }
            if !ua && !ub {
                removed += 1;
            }
        }
        i += 1;
    }

    i = 0;
    while i < m {
        if edges[i][0] == 1 {
            let u = edges[i][1];
            let v = edges[i][2];

            if dsu_union(&mut parent_a, &mut rank_a, u, v) {
                comp_a -= 1;
            } else {
                removed += 1;
            }
        }
        i += 1;
    }

    i = 0;
    while i < m {
        if edges[i][0] == 2 {
            let u = edges[i][1];
            let v = edges[i][2];

            if dsu_union(&mut parent_b, &mut rank_b, u, v) {
                comp_b -= 1;
            } else {
                removed += 1;
            }
        }
        i += 1;
    }

    if comp_a == 1 && comp_b == 1 {
        removed
    } else {
        -1
    }
}
