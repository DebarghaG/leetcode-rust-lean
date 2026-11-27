fn find_index(labels: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = labels.len();
    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if labels[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

pub fn count_good_nodes(edges: &[Vec<i64>]) -> i64 {
    let n: usize = edges.len() + 1;

    let mut labels: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut li: i64 = 0;
    while i < n {
        labels.push(li);
        i += 1;
        li += 1;
    }

    let mut adj: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < n {
        let row: Vec<i64> = Vec::new();
        adj.push(row);
        i += 1;
    }

    i = 0;
    while i < edges.len() {
        let row = &edges[i];
        let a_i = row[0];
        let b_i = row[1];
        let a = find_index(&labels, a_i);
        let b = find_index(&labels, b_i);
        adj[a].push(b_i);
        adj[b].push(a_i);
        i += 1;
    }

    let mut st_u: Vec<i64> = Vec::new();
    let mut st_p: Vec<i64> = Vec::new();
    let mut st_j: Vec<i64> = Vec::new();
    let mut st_total: Vec<i64> = Vec::new();
    let mut st_first: Vec<i64> = Vec::new();
    let mut st_ok: Vec<bool> = Vec::new();

    st_u.push(0);
    st_p.push(-1);
    st_j.push(0);
    st_total.push(1);
    st_first.push(-1);
    st_ok.push(true);

    let mut good: i64 = 0;

    while st_u.len() > 0 {
        let top: usize = st_u.len() - 1;
        let u_i: i64 = st_u[top];
        let p_i: i64 = st_p[top];
        let j_i: i64 = st_j[top];
        let total: i64 = st_total[top];
        let first: i64 = st_first[top];
        let ok: bool = st_ok[top];

        st_u.pop();
        st_p.pop();
        st_j.pop();
        st_total.pop();
        st_first.pop();
        st_ok.pop();

        let u_idx: usize = find_index(&labels, u_i);
        let degree: usize = adj[u_idx].len();
        let j_usize: usize = find_index(&labels, j_i);

        if j_usize < degree {
            let v_i: i64 = adj[u_idx][j_usize];

            st_u.push(u_i);
            st_p.push(p_i);
            st_j.push(j_i + 1);
            st_total.push(total);
            st_first.push(first);
            st_ok.push(ok);

            if v_i != p_i {
                st_u.push(v_i);
                st_p.push(u_i);
                st_j.push(0);
                st_total.push(1);
                st_first.push(-1);
                st_ok.push(true);
            }
        } else {
            if ok {
                good += 1;
            }

            if p_i != -1 {
                let ptop: usize = st_u.len() - 1;
                let pu_i: i64 = st_u[ptop];
                let pp_i: i64 = st_p[ptop];
                let pj_i: i64 = st_j[ptop];
                let ptotal: i64 = st_total[ptop];
                let pfirst: i64 = st_first[ptop];
                let pok: bool = st_ok[ptop];

                st_u.pop();
                st_p.pop();
                st_j.pop();
                st_total.pop();
                st_first.pop();
                st_ok.pop();

                let ntotal: i64 = ptotal + total;
                let mut nfirst: i64 = pfirst;
                let mut nok: bool = pok;

                if nfirst == -1 {
                    nfirst = total;
                } else {
                    if nfirst != total {
                        nok = false;
                    }
                }

                st_u.push(pu_i);
                st_p.push(pp_i);
                st_j.push(pj_i);
                st_total.push(ntotal);
                st_first.push(nfirst);
                st_ok.push(nok);
            }
        }
    }

    good
}
