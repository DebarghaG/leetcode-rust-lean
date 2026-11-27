fn seg_update(seg_max: &mut Vec<i64>, size: usize, coord: usize, gap: i64) {
    let mut p = size + coord;
    seg_max[p] = gap;
    p >>= 1;

    while p > 0 {
        let left = p << 1;
        let right = left + 1;

        let lv = seg_max[left];
        let rv = seg_max[right];

        if lv >= rv {
            seg_max[p] = lv;
        } else {
            seg_max[p] = rv;
        }

        p >>= 1;
    }
}

fn find(parent: &mut Vec<i64>, x: usize) -> usize {
    let mut root = x;
    while parent[root] as usize != root {
        root = parent[root] as usize;
    }

    let mut cur = x;
    while parent[cur] as usize != cur {
        let nxt = parent[cur] as usize;
        parent[cur] = root as i64;
        cur = nxt;
    }

    root
}

pub fn get_results(queries: &[Vec<i64>]) -> Vec<bool> {
    let n = queries.len();

    let mut max_coord: usize = 0;
    let mut type2_count: usize = 0;

    let mut i = 0;
    while i < n {
        let typ = queries[i][0];
        let x = queries[i][1] as usize;

        if x > max_coord {
            max_coord = x;
        }
        if typ == 2 {
            type2_count += 1;
        }

        i += 1;
    }

    let mut present: Vec<bool> = Vec::new();
    let mut c = 0;
    while c <= max_coord {
        present.push(false);
        c += 1;
    }

    i = 0;
    while i < n {
        if queries[i][0] == 1 {
            let x = queries[i][1] as usize;
            present[x] = true;
        }
        i += 1;
    }

    let mut idx_at: Vec<i64> = Vec::new();
    c = 0;
    while c <= max_coord {
        idx_at.push(-1);
        c += 1;
    }

    let mut obstacles: Vec<i64> = Vec::new();
    let mut parent: Vec<i64> = Vec::new();

    c = 0;
    while c <= max_coord {
        if present[c] {
            idx_at[c] = obstacles.len() as i64;
            obstacles.push(c as i64);
        }

        if c == 0 {
            parent.push(0);
        } else if present[c] {
            parent.push(c as i64);
        } else {
            parent.push(parent[c - 1]);
        }

        c += 1;
    }

    let k = obstacles.len();
    let k_i = k as i64;

    let mut prev: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();

    let mut j = 0;
    while j < k {
        if j == 0 {
            prev.push(-1);
        } else {
            prev.push(j as i64 - 1);
        }

        if j + 1 < k {
            next.push(j as i64 + 1);
        } else {
            next.push(k_i);
        }

        j += 1;
    }

    let mut size: usize = 1;
    while size < max_coord + 1 {
        size = size << 1;
    }

    let total = size << 1;
    let mut seg_max: Vec<i64> = Vec::new();

    let mut t = 0;
    while t < total {
        seg_max.push(0);
        t += 1;
    }

    j = 0;
    while j < k {
        let coord = obstacles[j] as usize;
        let gap = if j == 0 {
            obstacles[j]
        } else {
            obstacles[j] - obstacles[j - 1]
        };

        seg_max[size + coord] = gap;
        j += 1;
    }

    let mut p = size - 1;
    while p > 0 {
        let left = p << 1;
        let right = left + 1;

        let lv = seg_max[left];
        let rv = seg_max[right];

        if lv >= rv {
            seg_max[p] = lv;
        } else {
            seg_max[p] = rv;
        }

        p -= 1;
    }

    let mut ans: Vec<bool> = Vec::new();
    let mut ai = 0;
    while ai < type2_count {
        ans.push(false);
        ai += 1;
    }

    let mut ans_idx = type2_count;
    let mut qi = n;

    while qi > 0 {
        qi -= 1;

        let typ = queries[qi][0];

        if typ == 1 {
            let x = queries[qi][1] as usize;
            let jj = idx_at[x];
            let j = jj as usize;

            let pidx = prev[j];
            let sidx = next[j];

            if sidx < k_i {
                let si = sidx as usize;
                let succ_coord = obstacles[si] as usize;

                let pred_coord: i64 = if pidx >= 0 {
                    obstacles[pidx as usize]
                } else {
                    0
                };

                let new_gap = obstacles[si] - pred_coord;
                seg_update(&mut seg_max, size, succ_coord, new_gap);
            }

            if pidx >= 0 {
                next[pidx as usize] = sidx;
            }
            if sidx < k_i {
                prev[sidx as usize] = pidx;
            }

            let pred_active = find(&mut parent, x - 1);
            parent[x] = pred_active as i64;
        } else {
            let x = queries[qi][1] as usize;
            let sz = queries[qi][2];

            let last = find(&mut parent, x) as i64;

            let mut l = size;
            let mut r = size + x + 1;
            let mut best: i64 = 0;

            while l < r {
                if (l & 1) == 1 {
                    let val = seg_max[l];
                    if val > best {
                        best = val;
                    }
                    l += 1;
                }

                if (r & 1) == 1 {
                    r -= 1;
                    let val = seg_max[r];
                    if val > best {
                        best = val;
                    }
                }

                l >>= 1;
                r >>= 1;
            }

            let tail = x as i64 - last;
            if tail > best {
                best = tail;
            }

            ans_idx -= 1;
            ans[ans_idx] = best >= sz;
        }
    }

    ans
}
