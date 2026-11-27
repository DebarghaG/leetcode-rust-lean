#[macro_export]
macro_rules! vec {
    () => {
        ::std::vec::Vec::<::std::vec::Vec<i64>>::new()
    };
    ($elem:expr; $n:expr) => {
        ::std::vec![$elem; $n]
    };
    ($($x:expr),+ $(,)?) => {{
        let mut __v = ::std::vec::Vec::new();
        $( __v.push($x); )+
        __v
    }};
}

fn topo_sort(k: i64, conditions: &[Vec<i64>]) -> Vec<i64> {
    let n: usize = k as usize;

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut indeg: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        adj.push(Vec::new());
        indeg.push(0);
        i += 1;
    }

    let m: usize = conditions.len();
    i = 0;
    while i < m {
        let u: usize = (conditions[i][0] - 1) as usize;
        let v: i64 = conditions[i][1] - 1;
        let vi: usize = v as usize;
        adj[u].push(v);
        indeg[vi] = indeg[vi] + 1;
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        if indeg[i] == 0 {
            queue.push(i as i64);
        }
        i += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut head: usize = 0;
    while head < queue.len() {
        let u: i64 = queue[head];
        head += 1;
        order.push(u + 1);

        let ui: usize = u as usize;
        let deg: usize = adj[ui].len();
        let mut e: usize = 0;
        while e < deg {
            let w: i64 = adj[ui][e];
            let wi: usize = w as usize;
            indeg[wi] = indeg[wi] - 1;
            if indeg[wi] == 0 {
                queue.push(w);
            }
            e += 1;
        }
    }

    order
}

pub fn build_matrix(k: i64, row_conditions: &[Vec<i64>], col_conditions: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n: usize = k as usize;

    let row_order: Vec<i64> = topo_sort(k, row_conditions);
    let col_order: Vec<i64> = topo_sort(k, col_conditions);

    if row_order.len() < n {
        let empty: Vec<Vec<i64>> = Vec::new();
        return empty;
    }
    if col_order.len() < n {
        let empty: Vec<Vec<i64>> = Vec::new();
        return empty;
    }

    let mut col_pos: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        col_pos.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let val: i64 = col_order[i];
        let vi: usize = (val - 1) as usize;
        col_pos[vi] = i as i64;
        i += 1;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let val: i64 = row_order[i];
        let vi: usize = (val - 1) as usize;
        let c: usize = col_pos[vi] as usize;

        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n {
            if j == c {
                row.push(val);
            } else {
                row.push(0);
            }
            j += 1;
        }
        out.push(row);
        i += 1;
    }

    out
}
