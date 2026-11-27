pub fn cut_off_tree(forest: &[Vec<i64>]) -> i64 {
    let m = forest.len();
    if m == 0 {
        return 0;
    }
    let n = forest[0].len();
    if n == 0 {
        return 0;
    }

    let mut heights: Vec<i64> = Vec::new();
    let mut rows: Vec<usize> = Vec::new();
    let mut cols: Vec<usize> = Vec::new();

    let mut i = 0;
    while i < m {
        let mut j = 0;
        while j < n {
            let v = forest[i][j];
            if v > 1 {
                heights.push(v);
                rows.push(i);
                cols.push(j);
            }
            j += 1;
        }
        i += 1;
    }

    let k = heights.len();

    // Insertion sort by tree height, keeping row and column arrays aligned.
    let mut a = 1;
    while a < k {
        let h = heights[a];
        let r = rows[a];
        let c = cols[a];
        let mut b = a;

        while b > 0 {
            if heights[b - 1] <= h {
                break;
            }
            heights[b] = heights[b - 1];
            rows[b] = rows[b - 1];
            cols[b] = cols[b - 1];
            b -= 1;
        }

        heights[b] = h;
        rows[b] = r;
        cols[b] = c;
        a += 1;
    }

    let mut total: i64 = 0;
    let mut cur_r: usize = 0;
    let mut cur_c: usize = 0;

    let mut idx = 0;
    while idx < k {
        let d = bfs(forest, cur_r, cur_c, rows[idx], cols[idx]);
        if d < 0 {
            return -1;
        }
        total += d;
        cur_r = rows[idx];
        cur_c = cols[idx];
        idx += 1;
    }

    total
}

fn bfs(
    forest: &[Vec<i64>],
    start_r: usize,
    start_c: usize,
    target_r: usize,
    target_c: usize,
) -> i64 {
    let m = forest.len();
    if m == 0 {
        return -1;
    }
    let n = forest[0].len();
    if n == 0 {
        return -1;
    }

    let total_cells = m * n;
    let mut dist: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < total_cells {
        dist.push(-1);
        i += 1;
    }

    let start = start_r * n + start_c;
    let target = target_r * n + target_c;

    let mut queue: Vec<usize> = Vec::new();
    dist[start] = 0;
    queue.push(start);

    let mut head: usize = 0;
    while head < queue.len() {
        let cur = queue[head];
        head += 1;

        if cur == target {
            return dist[cur];
        }

        let r = cur / n;
        let c = cur % n;
        let dcur = dist[cur];

        if r > 0 {
            let nr = r - 1;
            let next = nr * n + c;
            if forest[nr][c] != 0 && dist[next] == -1 {
                dist[next] = dcur + 1;
                queue.push(next);
            }
        }

        if r + 1 < m {
            let nr = r + 1;
            let next = nr * n + c;
            if forest[nr][c] != 0 && dist[next] == -1 {
                dist[next] = dcur + 1;
                queue.push(next);
            }
        }

        if c > 0 {
            let nc = c - 1;
            let next = r * n + nc;
            if forest[r][nc] != 0 && dist[next] == -1 {
                dist[next] = dcur + 1;
                queue.push(next);
            }
        }

        if c + 1 < n {
            let nc = c + 1;
            let next = r * n + nc;
            if forest[r][nc] != 0 && dist[next] == -1 {
                dist[next] = dcur + 1;
                queue.push(next);
            }
        }
    }

    -1
}
