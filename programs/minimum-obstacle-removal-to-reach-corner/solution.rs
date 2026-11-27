fn relax(
    nr: usize,
    nc: usize,
    n: usize,
    d: i64,
    grid: &[Vec<i64>],
    dist: &mut Vec<i64>,
    cur: &mut Vec<i64>,
    next: &mut Vec<i64>,
) {
    let nidx = nr * n + nc;
    let cost = grid[nr][nc];
    let nd = d + cost;
    if nd < dist[nidx] {
        dist[nidx] = nd;
        if cost == 0 {
            cur.push(nidx as i64);
        } else {
            next.push(nidx as i64);
        }
    }
}

pub fn minimum_obstacles(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    let n = grid[0].len();
    let total = m * n;
    let inf = (total as i64) + 10;

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < total {
        dist.push(inf);
        i += 1;
    }
    dist[0] = 0;

    let mut cur: Vec<i64> = Vec::new();
    cur.push(0);
    let mut next: Vec<i64> = Vec::new();

    let mut d: i64 = 0;
    let mut done: bool = false;
    let mut answer: i64 = inf;

    while !done && d <= total as i64 {
        if cur.len() == 0 {
            done = true;
            answer = dist[total - 1];
        } else {
            let mut head: usize = 0;
            while head < cur.len() && !done {
                let idx = cur[head] as usize;
                head += 1;
                if dist[idx] == d {
                    if idx == total - 1 {
                        done = true;
                        answer = d;
                    } else {
                        let r = idx / n;
                        let c = idx % n;
                        if r > 0 {
                            relax(r - 1, c, n, d, grid, &mut dist, &mut cur, &mut next);
                        }
                        if r + 1 < m {
                            relax(r + 1, c, n, d, grid, &mut dist, &mut cur, &mut next);
                        }
                        if c > 0 {
                            relax(r, c - 1, n, d, grid, &mut dist, &mut cur, &mut next);
                        }
                        if c + 1 < n {
                            relax(r, c + 1, n, d, grid, &mut dist, &mut cur, &mut next);
                        }
                    }
                }
            }
            if !done {
                cur = next;
                next = Vec::new();
                d += 1;
            }
        }
    }

    answer
}
