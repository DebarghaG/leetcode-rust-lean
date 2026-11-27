pub fn check_ways(pairs: &[Vec<i64>]) -> i64 {
    let max_val: usize = 501;

    let mut idx_of: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < max_val {
        idx_of.push(-1i64);
        t += 1;
    }

    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < pairs.len() {
        let a = pairs[i][0] as usize;
        let b = pairs[i][1] as usize;
        if idx_of[a] == -1i64 {
            idx_of[a] = n as i64;
            n += 1;
        }
        if idx_of[b] == -1i64 {
            idx_of[b] = n as i64;
            n += 1;
        }
        i += 1;
    }

    if n == 0 {
        return 0;
    }

    let words: usize = (n + 63) / 64;
    let total_words: usize = n * words;

    let mut bits: Vec<i64> = Vec::new();
    i = 0;
    while i < total_words {
        bits.push(0i64);
        i += 1;
    }

    let mut degree: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        degree.push(0i64);
        i += 1;
    }

    i = 0;
    while i < pairs.len() {
        let av = pairs[i][0] as usize;
        let bv = pairs[i][1] as usize;
        let a = idx_of[av] as usize;
        let b = idx_of[bv] as usize;

        let aoff = a * words;
        let bword = b >> 6;
        let bbit = b & 63;
        bits[aoff + bword] = bits[aoff + bword] | (1i64 << bbit);

        let boff = b * words;
        let aword = a >> 6;
        let abit = a & 63;
        bits[boff + aword] = bits[boff + aword] | (1i64 << abit);

        degree[a] = degree[a] + 1;
        degree[b] = degree[b] + 1;

        i += 1;
    }

    let mut nodes: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        nodes.push(i as i64);
        i += 1;
    }

    i = 0;
    while i < n {
        let mut best: usize = i;
        let mut j: usize = i + 1;
        while j < n {
            let bj = nodes[j] as usize;
            let bb = nodes[best] as usize;
            if degree[bj] > degree[bb] {
                best = j;
            }
            j += 1;
        }
        if best != i {
            let tmp = nodes[i];
            nodes[i] = nodes[best];
            nodes[best] = tmp;
        }
        i += 1;
    }

    let n_i: i64 = n as i64;
    let root: usize = nodes[0] as usize;

    let mut ans: i64 = 1;
    let mut valid: bool = true;

    if degree[root] != n_i - 1 {
        valid = false;
    }

    let mut pos: usize = 0;
    while pos < n {
        if valid {
            let u = nodes[pos] as usize;
            let du = degree[u];
            let uoff = u * words;

            let mut parent: i64 = -1i64;
            let mut v: usize = 0;
            while v < n {
                let vword = v >> 6;
                let vbit = v & 63;
                if ((bits[uoff + vword] >> vbit) & 1i64) == 1i64 {
                    let dv = degree[v];
                    if dv >= du {
                        if parent == -1i64 {
                            parent = v as i64;
                        } else {
                            let p = parent as usize;
                            if dv < degree[p] {
                                parent = v as i64;
                            }
                        }
                    }
                }
                v += 1;
            }

            if parent == -1i64 {
                if du != n_i - 1 {
                    valid = false;
                }
            } else {
                let p = parent as usize;
                let poff = p * words;
                let mut y: usize = 0;
                while y < n {
                    if y != p {
                        let yword = y >> 6;
                        let ybit = y & 63;
                        let u_has = ((bits[uoff + yword] >> ybit) & 1i64) == 1i64;
                        if u_has {
                            let p_has = ((bits[poff + yword] >> ybit) & 1i64) == 1i64;
                            if !p_has {
                                valid = false;
                            }
                        }
                    }
                    y += 1;
                }
                if degree[p] == du {
                    ans = 2;
                }
            }
        }

        pos += 1;
    }

    if !valid {
        return 0;
    }
    ans
}
