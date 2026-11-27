fn contains(v: &Vec<i64>, id: i64) -> bool {
    let mut k: usize = 0;
    while k < v.len() {
        if v[k] == id {
            return true;
        }
        k += 1;
    }
    false
}

fn flood_fill(
    grid: &[Vec<i64>],
    labels: &mut Vec<i64>,
    queue: &mut Vec<usize>,
    n: usize,
    start: usize,
    id: i64,
) {
    let mut head: usize = 0;
    let mut tail: usize = 0;

    queue[tail] = start;
    tail += 1;
    labels[start] = id;

    while head < tail {
        let pu = queue[head];
        head += 1;
        let r = pu / n;
        let c = pu % n;

        if r > 0 && grid[r - 1][c] == 1 && labels[pu - n] == 0 {
            labels[pu - n] = id;
            queue[tail] = pu - n;
            tail += 1;
        }
        if r + 1 < n && grid[r + 1][c] == 1 && labels[pu + n] == 0 {
            labels[pu + n] = id;
            queue[tail] = pu + n;
            tail += 1;
        }
        if c > 0 && grid[r][c - 1] == 1 && labels[pu - 1] == 0 {
            labels[pu - 1] = id;
            queue[tail] = pu - 1;
            tail += 1;
        }
        if c + 1 < n && grid[r][c + 1] == 1 && labels[pu + 1] == 0 {
            labels[pu + 1] = id;
            queue[tail] = pu + 1;
            tail += 1;
        }
    }
}

fn label_islands(grid: &[Vec<i64>]) -> Vec<i64> {
    let n = grid.len();
    let nn = n * n;

    let mut labels: Vec<i64> = Vec::new();
    let mut queue: Vec<usize> = Vec::new();
    let mut t: usize = 0;
    while t < nn {
        labels.push(0);
        queue.push(0);
        t += 1;
    }

    let mut next_id: i64 = 1;
    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            let idx = i * n + j;
            if grid[i][j] == 1 && labels[idx] == 0 {
                flood_fill(grid, &mut labels, &mut queue, n, idx, next_id);
                next_id += 1;
            }
            j += 1;
        }
        i += 1;
    }

    labels
}

fn compute_areas(labels: &Vec<i64>) -> Vec<i64> {
    let nn = labels.len();

    let mut max_id: i64 = 0;
    let mut t: usize = 0;
    while t < nn {
        if labels[t] > max_id {
            max_id = labels[t];
        }
        t += 1;
    }

    let mut areas: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k <= max_id {
        areas.push(0);
        k += 1;
    }

    t = 0;
    while t < nn {
        let id = labels[t];
        if id > 0 {
            areas[id as usize] += 1;
        }
        t += 1;
    }

    areas
}

pub fn largest_island(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return 0;
    }

    let labels = label_islands(grid);
    let areas = compute_areas(&labels);

    let mut ans: i64 = 0;
    let mut k: usize = 1;
    while k < areas.len() {
        if areas[k] > ans {
            ans = areas[k];
        }
        k += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < n {
            if grid[i][j] == 0 {
                let mut ids: Vec<i64> = Vec::new();

                if i > 0 && grid[i - 1][j] == 1 {
                    let id = labels[(i - 1) * n + j];
                    if !contains(&ids, id) {
                        ids.push(id);
                    }
                }
                if i + 1 < n && grid[i + 1][j] == 1 {
                    let id = labels[(i + 1) * n + j];
                    if !contains(&ids, id) {
                        ids.push(id);
                    }
                }
                if j > 0 && grid[i][j - 1] == 1 {
                    let id = labels[i * n + (j - 1)];
                    if !contains(&ids, id) {
                        ids.push(id);
                    }
                }
                if j + 1 < n && grid[i][j + 1] == 1 {
                    let id = labels[i * n + (j + 1)];
                    if !contains(&ids, id) {
                        ids.push(id);
                    }
                }

                let mut local: i64 = 1;
                let mut q: usize = 0;
                while q < ids.len() {
                    local += areas[ids[q] as usize];
                    q += 1;
                }

                if local > ans {
                    ans = local;
                }
            }
            j += 1;
        }
        i += 1;
    }

    ans
}
