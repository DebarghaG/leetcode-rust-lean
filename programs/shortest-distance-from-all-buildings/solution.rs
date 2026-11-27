pub fn shortest_distance(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return -1;
    }
    let n = grid[0].len();
    if n == 0 {
        return -1;
    }

    let mut total: Vec<Vec<i64>> = Vec::new();
    let mut reach: Vec<Vec<i64>> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut total_row: Vec<i64> = Vec::new();
        let mut reach_row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            total_row.push(0);
            reach_row.push(0);
            j += 1;
        }
        total.push(total_row);
        reach.push(reach_row);
        i += 1;
    }

    let mut building_count: i64 = 0;

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if grid[i][j] == 1 {
                building_count += 1;

                let mut dist: Vec<Vec<i64>> = Vec::new();
                let mut a = 0;
                while a < m {
                    let mut dist_row: Vec<i64> = Vec::new();
                    let mut b = 0;
                    while b < n {
                        dist_row.push(-1);
                        b += 1;
                    }
                    dist.push(dist_row);
                    a += 1;
                }

                dist[i][j] = 0;

                let mut queue: Vec<usize> = Vec::new();
                queue.push(i * n + j);
                let mut head: usize = 0;

                while head < queue.len() {
                    let code = queue[head];
                    let r = code / n;
                    let c = code % n;
                    let next_dist = dist[r][c] + 1;

                    if r > 0 {
                        let nr = r - 1;
                        if grid[nr][c] == 0 && dist[nr][c] == -1 {
                            dist[nr][c] = next_dist;
                            queue.push(nr * n + c);
                        }
                    }

                    if r + 1 < m {
                        let nr = r + 1;
                        if grid[nr][c] == 0 && dist[nr][c] == -1 {
                            dist[nr][c] = next_dist;
                            queue.push(nr * n + c);
                        }
                    }

                    if c > 0 {
                        let nc = c - 1;
                        if grid[r][nc] == 0 && dist[r][nc] == -1 {
                            dist[r][nc] = next_dist;
                            queue.push(r * n + nc);
                        }
                    }

                    if c + 1 < n {
                        let nc = c + 1;
                        if grid[r][nc] == 0 && dist[r][nc] == -1 {
                            dist[r][nc] = next_dist;
                            queue.push(r * n + nc);
                        }
                    }

                    head += 1;
                }

                let mut x = 0;
                while x < m {
                    let mut y = 0;
                    while y < n {
                        if grid[x][y] == 0 && dist[x][y] >= 0 {
                            total[x][y] += dist[x][y];
                            reach[x][y] += 1;
                        }
                        y += 1;
                    }
                    x += 1;
                }
            }
            j += 1;
        }
        i += 1;
    }

    let mut best: i64 = -1;

    i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            if grid[i][j] == 0 && reach[i][j] == building_count {
                if best == -1 || total[i][j] < best {
                    best = total[i][j];
                }
            }
            j += 1;
        }
        i += 1;
    }

    best
}
