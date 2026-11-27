pub fn max_distance(grid: &[Vec<i64>]) -> i64 {
    let n = grid.len();
    if n == 0 {
        return -1;
    }

    let mut visited: Vec<bool> = Vec::new();
    let mut queue: Vec<i64> = Vec::new();
    let mut land_count: i64 = 0;
    let mut water_count: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let row = &grid[i];
        let mut j: usize = 0;
        while j < n {
            if row[j] == 1 {
                land_count += 1;
                visited.push(true);
                queue.push((i * n + j) as i64);
            } else {
                water_count += 1;
                visited.push(false);
            }
            j += 1;
        }
        i += 1;
    }

    if land_count == 0 || water_count == 0 {
        return -1;
    }

    let mut head: usize = 0;
    let mut level: i64 = 0;
    let mut max_level: i64 = -1;

    while head < queue.len() {
        let layer_end = queue.len();

        while head < layer_end {
            let cur_i = queue[head];
            let cur = cur_i as usize;
            head += 1;

            let r = cur / n;
            let c = cur % n;

            if r > 0 {
                let ni = cur - n;
                if !visited[ni] {
                    visited[ni] = true;
                    queue.push(ni as i64);
                }
            }

            if r + 1 < n {
                let ni = cur + n;
                if !visited[ni] {
                    visited[ni] = true;
                    queue.push(ni as i64);
                }
            }

            if c > 0 {
                let ni = cur - 1;
                if !visited[ni] {
                    visited[ni] = true;
                    queue.push(ni as i64);
                }
            }

            if c + 1 < n {
                let ni = cur + 1;
                if !visited[ni] {
                    visited[ni] = true;
                    queue.push(ni as i64);
                }
            }
        }

        if head < queue.len() {
            level += 1;
            max_level = level;
        }
    }

    max_level
}
