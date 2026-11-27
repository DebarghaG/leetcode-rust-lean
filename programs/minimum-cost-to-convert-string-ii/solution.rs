fn vec_u8_eq(a: &Vec<u8>, b: &Vec<u8>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn minimum_cost(
    source: &[u8],
    target: &[u8],
    original: &[Vec<u8>],
    changed: &[Vec<u8>],
    cost: &[i64],
) -> i64 {
    let inf: i64 = 1000000000000000000;

    let mut uniq: Vec<Vec<u8>> = Vec::new();
    let mut orig_ids: Vec<i64> = Vec::new();
    let mut ch_ids: Vec<i64> = Vec::new();

    let m: usize = original.len();
    let mut k: usize = 0;
    while k < m {
        let s = &original[k];
        let mut found: i64 = -1;
        let mut t: usize = 0;
        while t < uniq.len() {
            if found == -1 {
                if vec_u8_eq(&uniq[t], s) {
                    found = t as i64;
                }
            }
            t += 1;
        }
        if found == -1 {
            let mut v: Vec<u8> = Vec::new();
            let mut q: usize = 0;
            while q < s.len() {
                v.push(s[q]);
                q += 1;
            }
            uniq.push(v);
            found = (uniq.len() as i64) - 1;
        }
        orig_ids.push(found);

        let s2 = &changed[k];
        let mut found2: i64 = -1;
        let mut t2: usize = 0;
        while t2 < uniq.len() {
            if found2 == -1 {
                if vec_u8_eq(&uniq[t2], s2) {
                    found2 = t2 as i64;
                }
            }
            t2 += 1;
        }
        if found2 == -1 {
            let mut v2: Vec<u8> = Vec::new();
            let mut q2: usize = 0;
            while q2 < s2.len() {
                v2.push(s2[q2]);
                q2 += 1;
            }
            uniq.push(v2);
            found2 = (uniq.len() as i64) - 1;
        }
        ch_ids.push(found2);

        k += 1;
    }

    let u: usize = uniq.len();

    let mut dist: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i < u {
        let mut row: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < u {
            if i == j {
                row.push(0);
            } else {
                row.push(inf);
            }
            j += 1;
        }
        dist.push(row);
        i += 1;
    }

    k = 0;
    while k < m {
        if k < cost.len() {
            let a = orig_ids[k] as usize;
            let b = ch_ids[k] as usize;
            let c = cost[k];
            if c < dist[a][b] {
                dist[a][b] = c;
            }
        }
        k += 1;
    }

    let mut mid: usize = 0;
    while mid < u {
        let mut x: usize = 0;
        while x < u {
            let mut y: usize = 0;
            while y < u {
                if dist[x][mid] < inf && dist[mid][y] < inf {
                    let nd = dist[x][mid] + dist[mid][y];
                    if nd < dist[x][y] {
                        dist[x][y] = nd;
                    }
                }
                y += 1;
            }
            x += 1;
        }
        mid += 1;
    }

    let mut children: Vec<Vec<i64>> = Vec::new();
    let mut terminal: Vec<i64> = Vec::new();

    let mut root: Vec<i64> = Vec::new();
    let mut r: usize = 0;
    while r < 26 {
        root.push(-1);
        r += 1;
    }
    children.push(root);
    terminal.push(-1);

    let mut sid: usize = 0;
    while sid < u {
        let mut node: usize = 0;
        let mut pos: usize = 0;
        while pos < uniq[sid].len() {
            let c = (uniq[sid][pos] - b'a') as usize;
            let mut nxt = children[node][c];
            if nxt == -1 {
                let new_idx = children.len() as i64;
                let mut row: Vec<i64> = Vec::new();
                let mut rr: usize = 0;
                while rr < 26 {
                    row.push(-1);
                    rr += 1;
                }
                children.push(row);
                terminal.push(-1);
                children[node][c] = new_idx;
                nxt = new_idx;
            }
            node = nxt as usize;
            pos += 1;
        }
        terminal[node] = sid as i64;
        sid += 1;
    }

    let mut max_len: usize = 0;
    let mut q: usize = 0;
    while q < u {
        if uniq[q].len() > max_len {
            max_len = uniq[q].len();
        }
        q += 1;
    }

    let n: usize = source.len();

    let mut dp: Vec<i64> = Vec::new();
    let mut d: usize = 0;
    while d <= n {
        dp.push(inf);
        d += 1;
    }
    dp[0] = 0;

    let mut src_ids: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z <= max_len {
        src_ids.push(-1);
        z += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let cur = dp[i];
        if cur < inf {
            if source[i] == target[i] {
                if cur < dp[i + 1] {
                    dp[i + 1] = cur;
                }
            }

            let mut rr: usize = 0;
            while rr <= max_len {
                src_ids[rr] = -1;
                rr += 1;
            }

            let mut node: usize = 0;
            let mut pos: usize = i;
            let mut alive: bool = true;
            while pos < n && alive {
                let c = (source[pos] - b'a') as usize;
                let nxt = children[node][c];
                if nxt == -1 {
                    alive = false;
                } else {
                    node = nxt as usize;
                    let l = pos - i + 1;
                    let tid = terminal[node];
                    if tid >= 0 && l <= max_len {
                        src_ids[l] = tid;
                    }
                    pos += 1;
                }
            }

            node = 0;
            pos = i;
            alive = true;
            while pos < n && alive {
                let c = (target[pos] - b'a') as usize;
                let nxt = children[node][c];
                if nxt == -1 {
                    alive = false;
                } else {
                    node = nxt as usize;
                    let l = pos - i + 1;
                    let tid = terminal[node];
                    if tid >= 0 && l <= max_len {
                        let from = src_ids[l];
                        if from >= 0 {
                            let dc = dist[from as usize][tid as usize];
                            if dc < inf {
                                let nc = cur + dc;
                                if nc < dp[i + l] {
                                    dp[i + l] = nc;
                                }
                            }
                        }
                    }
                    pos += 1;
                }
            }
        }
        i += 1;
    }

    if dp[n] >= inf {
        -1
    } else {
        dp[n]
    }
}
