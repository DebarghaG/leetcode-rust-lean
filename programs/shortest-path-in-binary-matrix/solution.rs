pub fn shortest_path_binary_matrix(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return -1;
    }
    if grid[0][0] != 0 {
        return -1;
    }
    if grid[n - 1][n - 1] != 0 {
        return -1;
    }

    let mut dist: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n * n {
        dist.push(-1);
        i += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    queue.push(0);
    dist[0] = 1;

    let mut head: usize = 0;
    let n_i = n as i64;

    while head < queue.len() {
        let cur = queue[head] as usize;
        head += 1;

        let r = cur / n;
        let c = cur % n;
        let d = dist[cur];

        if r == n - 1 && c == n - 1 {
            return d;
        }

        let r_i = r as i64;
        let c_i = c as i64;

        let mut di: i64 = -1;
        while di <= 1 {
            let mut dj: i64 = -1;
            while dj <= 1 {
                if !(di == 0 && dj == 0) {
                    let nr = r_i + di;
                    let nc = c_i + dj;

                    if nr >= 0 && nr < n_i && nc >= 0 && nc < n_i {
                        let nidx_i64 = nr * n_i + nc;
                        let nidx = nidx_i64 as usize;

                        if grid[nr as usize][nc as usize] == 0 && dist[nidx] == -1 {
                            dist[nidx] = d + 1;
                            queue.push(nidx_i64);
                        }
                    }
                }
                dj += 1;
            }
            di += 1;
        }
    }

    -1
}
