fn find_next(parent: &mut Vec<i64>, base: usize, start: usize) -> usize {
    let mut v = start;
    while parent[base + v] != v as i64 {
        v = parent[base + v] as usize;
    }

    let root = v;
    let mut u = start;
    while u != root {
        let nxt = parent[base + u] as usize;
        parent[base + u] = root as i64;
        u = nxt;
    }

    root
}

pub fn minimum_visited_cells(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    if m == 0 {
        return -1;
    }

    let n = grid[0].len();
    if n == 0 {
        return -1;
    }

    let total = m * n;

    let mut dist: Vec<i64> = Vec::new();
    let mut t = 0;
    while t < total {
        dist.push(-1);
        t += 1;
    }

    let row_stride = n + 1;
    let col_stride = m + 1;

    // For each row, row_next[i * row_stride + c] stores the next
    // still-unvisited column at or after c in that row.
    let mut row_next: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut c = 0;
        while c <= n {
            row_next.push(c as i64);
            c += 1;
        }
        i += 1;
    }

    // For each column, col_next[j * col_stride + r] stores the next
    // still-unvisited row at or after r in that column.
    let mut col_next: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        let mut r = 0;
        while r <= m {
            col_next.push(r as i64);
            r += 1;
        }
        j += 1;
    }

    let mut queue: Vec<i64> = Vec::new();
    dist[0] = 1;
    queue.push(0);

    let target = (m - 1) * n + (n - 1);
    let mut head = 0usize;

    while head < queue.len() {
        let encoded = queue[head];
        head += 1;

        let cell = encoded as usize;
        let d = dist[cell];

        if cell == target {
            return d;
        }

        let row = cell / n;
        let col = cell % n;
        let reach = grid[row][col];

        let row_base = row * row_stride;

        let mut max_col = col;
        let reach_col = (col as i64) + reach;
        if reach_col >= (n as i64) - 1 {
            max_col = n - 1;
        } else {
            max_col = reach_col as usize;
        }

        let mut c = find_next(&mut row_next, row_base, col + 1);
        while c <= max_col {
            let next_cell = row * n + c;
            if dist[next_cell] == -1 {
                dist[next_cell] = d + 1;
                queue.push(next_cell as i64);
            }

            let next_c = find_next(&mut row_next, row_base, c + 1);
            row_next[row_base + c] = next_c as i64;

            let col_base_c = c * col_stride;
            let next_r = find_next(&mut col_next, col_base_c, row + 1);
            col_next[col_base_c + row] = next_r as i64;

            c = next_c;
        }

        let col_base = col * col_stride;

        let mut max_row = row;
        let reach_row = (row as i64) + reach;
        if reach_row >= (m as i64) - 1 {
            max_row = m - 1;
        } else {
            max_row = reach_row as usize;
        }

        let mut r = find_next(&mut col_next, col_base, row + 1);
        while r <= max_row {
            let next_cell = r * n + col;
            if dist[next_cell] == -1 {
                dist[next_cell] = d + 1;
                queue.push(next_cell as i64);
            }

            let next_r = find_next(&mut col_next, col_base, r + 1);
            col_next[col_base + r] = next_r as i64;

            let row_base_r = r * row_stride;
            let next_c = find_next(&mut row_next, row_base_r, col + 1);
            row_next[row_base_r + col] = next_c as i64;

            r = next_r;
        }
    }

    dist[target]
}
