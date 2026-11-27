fn popcount(mut x: usize) -> i64 {
    let mut c: i64 = 0;
    while x > 0 {
        if (x & 1) == 1 {
            c += 1;
        }
        x = x >> 1;
    }
    c
}

pub fn supersequences(words: &[Vec<u8>]) -> Vec<Vec<i64>> {
    let mut id: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < 26 {
        id.push(-1);
        i += 1;
    }

    let mut rev: Vec<usize> = Vec::new();
    let mut m: usize = 0;

    let mut wi: usize = 0;
    while wi < words.len() {
        let w = &words[wi];

        let c0 = (w[0] as usize) - 97;
        if id[c0] == -1 {
            id[c0] = m as i64;
            rev.push(c0);
            m += 1;
        }

        let c1 = (w[1] as usize) - 97;
        if id[c1] == -1 {
            id[c1] = m as i64;
            rev.push(c1);
            m += 1;
        }

        wi += 1;
    }

    let mut adj: Vec<Vec<i64>> = Vec::new();
    let mut r: usize = 0;
    while r < m {
        let mut row: Vec<i64> = Vec::new();
        let mut c: usize = 0;
        while c < m {
            row.push(0);
            c += 1;
        }
        adj.push(row);
        r += 1;
    }

    wi = 0;
    while wi < words.len() {
        let w = &words[wi];
        let a = id[(w[0] as usize) - 97] as usize;
        let b = id[(w[1] as usize) - 97] as usize;
        adj[a][b] = 1;
        wi += 1;
    }

    let total: usize = 1 << m;
    let mut min_extra: i64 = 1000000;
    let mut masks: Vec<usize> = Vec::new();

    let mut mask: usize = 0;
    while mask < total {
        let mut indeg: Vec<i64> = Vec::new();
        let mut v: usize = 0;
        while v < m {
            indeg.push(0);
            v += 1;
        }

        v = 0;
        while v < m {
            if (mask & (1 << v)) == 0 {
                let mut u: usize = 0;
                while u < m {
                    if (mask & (1 << u)) == 0 && adj[u][v] == 1 {
                        indeg[v] += 1;
                    }
                    u += 1;
                }
            }
            v += 1;
        }

        let mut queue: Vec<usize> = Vec::new();
        v = 0;
        while v < m {
            if (mask & (1 << v)) == 0 && indeg[v] == 0 {
                queue.push(v);
            }
            v += 1;
        }

        let mut processed: i64 = 0;
        let mut qi: usize = 0;
        while qi < queue.len() {
            let u = queue[qi];
            qi += 1;
            processed += 1;

            let mut w: usize = 0;
            while w < m {
                if (mask & (1 << w)) == 0 && adj[u][w] == 1 {
                    indeg[w] -= 1;
                    if indeg[w] == 0 {
                        queue.push(w);
                    }
                }
                w += 1;
            }
        }

        let mut active: i64 = 0;
        v = 0;
        while v < m {
            if (mask & (1 << v)) == 0 {
                active += 1;
            }
            v += 1;
        }

        if processed == active {
            let extra = popcount(mask);
            if extra < min_extra {
                min_extra = extra;
                masks.clear();
                masks.push(mask);
            } else if extra == min_extra {
                masks.push(mask);
            }
        }

        mask += 1;
    }

    let mut result: Vec<Vec<i64>> = Vec::new();
    let mut mi: usize = 0;
    while mi < masks.len() {
        let cur_mask = masks[mi];

        let mut freq: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < 26 {
            freq.push(0);
            k += 1;
        }

        let mut v: usize = 0;
        while v < m {
            let letter = rev[v];
            let mut cnt: i64 = 1;
            if (cur_mask & (1 << v)) != 0 {
                cnt += 1;
            }
            freq[letter] = cnt;
            v += 1;
        }

        result.push(freq);
        mi += 1;
    }

    result
}
