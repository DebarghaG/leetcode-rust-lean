pub fn all_cells_dist_order(rows: i64, cols: i64, rCenter: i64, cCenter: i64) -> Vec<Vec<i64>> {
    let total = rows * cols;

    let mut visited: Vec<bool> = Vec::new();
    let mut i: i64 = 0;
    while i < total {
        visited.push(false);
        i += 1;
    }

    let start = rCenter * cols + cCenter;
    visited[start as usize] = true;

    let mut queue: Vec<i64> = Vec::new();
    queue.push(start);
    let mut head: usize = 0;

    let mut out: Vec<Vec<i64>> = Vec::new();

    while head < queue.len() {
        let idx = queue[head];
        head += 1;

        let r = idx / cols;
        let c = idx % cols;

        let mut cell: Vec<i64> = Vec::new();
        cell.push(r);
        cell.push(c);
        out.push(cell);

        // up
        if r > 0 {
            let nidx = (r - 1) * cols + c;
            let ni = nidx as usize;
            if !visited[ni] {
                visited[ni] = true;
                queue.push(nidx);
            }
        }

        // right
        if c + 1 < cols {
            let nidx = r * cols + (c + 1);
            let ni = nidx as usize;
            if !visited[ni] {
                visited[ni] = true;
                queue.push(nidx);
            }
        }

        // down
        if r + 1 < rows {
            let nidx = (r + 1) * cols + c;
            let ni = nidx as usize;
            if !visited[ni] {
                visited[ni] = true;
                queue.push(nidx);
            }
        }

        // left
        if c > 0 {
            let nidx = r * cols + (c - 1);
            let ni = nidx as usize;
            if !visited[ni] {
                visited[ni] = true;
                queue.push(nidx);
            }
        }
    }

    out
}
