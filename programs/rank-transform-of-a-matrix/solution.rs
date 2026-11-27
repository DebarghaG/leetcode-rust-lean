fn dsu_find(parent: &[usize], x: usize) -> usize {
    let mut y = x;
    while parent[y] != y {
        y = parent[y];
    }
    y
}

fn dsu_union(parent: &mut Vec<usize>, size: &mut Vec<usize>, a: usize, b: usize) {
    let ra = dsu_find(&parent[..], a);
    let rb = dsu_find(&parent[..], b);

    if ra != rb {
        if size[ra] < size[rb] {
            parent[ra] = rb;
            size[rb] = size[rb] + size[ra];
        } else {
            parent[rb] = ra;
            size[ra] = size[ra] + size[rb];
        }
    }
}

pub fn matrix_rank_transform(matrix: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let m = matrix.len();
    if m == 0 {
        return Vec::new();
    }

    let n = matrix[0].len();
    if n == 0 {
        let mut out: Vec<Vec<i64>> = Vec::new();
        let mut i = 0;
        while i < m {
            let row: Vec<i64> = Vec::new();
            out.push(row);
            i += 1;
        }
        return out;
    }

    let total = m * n;
    let base = (total + 1) as i64;
    let offset = 1_000_000_000i64;

    let mut encoded: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let row = &matrix[i];
        let mut j = 0;
        while j < n {
            let idx = i * n + j;
            let v = row[j];
            encoded.push((v + offset) * base + (idx as i64));
            j += 1;
        }
        i += 1;
    }

    encoded.sort();

    let mut row_max: Vec<i64> = Vec::new();
    let mut col_max: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < m {
        row_max.push(0);
        k += 1;
    }
    k = 0;
    while k < n {
        col_max.push(0);
        k += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    k = 0;
    while k < total {
        ans.push(0);
        k += 1;
    }

    let nodes = m + n;
    let mut parent: Vec<usize> = Vec::new();
    let mut dsu_size: Vec<usize> = Vec::new();
    let mut parent_seen: Vec<usize> = Vec::new();
    let mut comp_max: Vec<i64> = Vec::new();
    let mut comp_seen: Vec<usize> = Vec::new();

    k = 0;
    while k < nodes {
        parent.push(0);
        dsu_size.push(0);
        parent_seen.push(0);
        comp_max.push(0);
        comp_seen.push(0);
        k += 1;
    }

    let encoded_len = encoded.len();
    let mut gid: usize = 0;
    let mut start = 0;

    while start < encoded_len {
        let first_code = encoded[start];
        let value = first_code / base - offset;

        let mut end = start + 1;
        while end < encoded_len {
            let next_value = encoded[end] / base - offset;
            if next_value != value {
                break;
            }
            end += 1;
        }

        gid += 1;

        // Union all rows/cols touched by this value group.
        let mut pos = start;
        while pos < end {
            let code = encoded[pos];
            let idx = (code % base) as usize;
            let r = idx / n;
            let c = idx % n;
            let rn = r;
            let cn = m + c;

            if parent_seen[rn] != gid {
                parent_seen[rn] = gid;
                parent[rn] = rn;
                dsu_size[rn] = 1;
            }

            if parent_seen[cn] != gid {
                parent_seen[cn] = gid;
                parent[cn] = cn;
                dsu_size[cn] = 1;
            }

            dsu_union(&mut parent, &mut dsu_size, rn, cn);
            pos += 1;
        }

        // Compute the max rank prefix for each connected component.
        pos = start;
        while pos < end {
            let code = encoded[pos];
            let idx = (code % base) as usize;
            let r = idx / n;
            let c = idx % n;

            let root = dsu_find(&parent[..], r);
            let rv = row_max[r];
            let cv = col_max[c];
            let best = if rv > cv { rv } else { cv };

            if comp_seen[root] != gid {
                comp_seen[root] = gid;
                comp_max[root] = best;
            } else if best > comp_max[root] {
                comp_max[root] = best;
            }

            pos += 1;
        }

        // Assign ranks.
        pos = start;
        while pos < end {
            let code = encoded[pos];
            let idx = (code % base) as usize;
            let r = idx / n;
            let c = idx % n;

            let root = dsu_find(&parent[..], r);
            let rank = comp_max[root] + 1;

            ans[idx] = rank;

            if row_max[r] < rank {
                row_max[r] = rank;
            }
            if col_max[c] < rank {
                col_max[c] = rank;
            }

            pos += 1;
        }

        start = end;
    }

    let mut out: Vec<Vec<i64>> = Vec::new();
    i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(ans[i * n + j]);
            j += 1;
        }
        out.push(row);
        i += 1;
    }

    out
}
