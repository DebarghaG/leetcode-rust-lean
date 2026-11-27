pub fn hit_bricks(grid: &[Vec<i64>], hits: &[Vec<i64>]) -> Vec<i64> {
    let m = grid.len();
    let n = grid[0].len();
    let total = m * n;
    let top = total;

    let mut active: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            active.push(grid[i][j]);
            j += 1;
        }
        i += 1;
    }

    let mut h = 0;
    while h < hits.len() {
        let r = hits[h][0] as usize;
        let c = hits[h][1] as usize;
        if grid[r][c] == 1 {
            active[r * n + c] = 0;
        }
        h += 1;
    }

    let mut parent: Vec<i64> = Vec::new();
    let mut size: Vec<i64> = Vec::new();
    let mut k = 0;
    while k <= total {
        parent.push(k as i64);
        size.push(1);
        k += 1;
    }

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let id = i * n + j;
            if active[id] == 1 {
                if i == 0 {
                    dsu_union(&mut parent, &mut size, id, top);
                }
                if i > 0 {
                    let up = (i - 1) * n + j;
                    if active[up] == 1 {
                        dsu_union(&mut parent, &mut size, id, up);
                    }
                }
                if j > 0 {
                    let left = id - 1;
                    if active[left] == 1 {
                        dsu_union(&mut parent, &mut size, id, left);
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < hits.len() {
        ans.push(0);
        z += 1;
    }

    let mut idx = hits.len();
    while idx > 0 {
        idx -= 1;

        let r = hits[idx][0] as usize;
        let c = hits[idx][1] as usize;
        let id = r * n + c;

        if grid[r][c] == 1 && active[id] == 0 {
            let old_root = dsu_find(&mut parent, top);
            let old_stable = size[old_root] - 1;

            active[id] = 1;

            if r == 0 {
                dsu_union(&mut parent, &mut size, id, top);
            }
            if r > 0 {
                let up = (r - 1) * n + c;
                if active[up] == 1 {
                    dsu_union(&mut parent, &mut size, id, up);
                }
            }
            if r + 1 < m {
                let down = (r + 1) * n + c;
                if active[down] == 1 {
                    dsu_union(&mut parent, &mut size, id, down);
                }
            }
            if c > 0 {
                let left = id - 1;
                if active[left] == 1 {
                    dsu_union(&mut parent, &mut size, id, left);
                }
            }
            if c + 1 < n {
                let right = id + 1;
                if active[right] == 1 {
                    dsu_union(&mut parent, &mut size, id, right);
                }
            }

            let new_root = dsu_find(&mut parent, top);
            let new_stable = size[new_root] - 1;
            let diff = new_stable - old_stable - 1;

            if diff > 0 {
                ans[idx] = diff;
            } else {
                ans[idx] = 0;
            }
        }
    }

    ans
}

fn dsu_find(parent: &mut Vec<i64>, x: usize) -> usize {
    let mut y = x;
    while parent[y] != y as i64 {
        y = parent[y] as usize;
    }

    let root = y;
    let mut z = x;
    while z != root {
        let nxt = parent[z] as usize;
        parent[z] = root as i64;
        z = nxt;
    }

    root
}

fn dsu_union(parent: &mut Vec<i64>, size: &mut Vec<i64>, a: usize, b: usize) {
    let mut ra = dsu_find(parent, a);
    let mut rb = dsu_find(parent, b);

    if ra != rb {
        if size[ra] < size[rb] {
            let tmp = ra;
            ra = rb;
            rb = tmp;
        }

        parent[rb] = ra as i64;
        size[ra] = size[ra] + size[rb];
    }
}
