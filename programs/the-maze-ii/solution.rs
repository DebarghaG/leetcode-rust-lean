pub fn shortest_distance(maze: &[Vec<i64>], start: &[i64], destination: &[i64]) -> i64 {
    let m = maze.len();
    let n = maze[0].len();
    let n_i = n as i64;

    let sr = start[0] as usize;
    let sc = start[1] as usize;
    let dr_dest = destination[0] as usize;
    let dc_dest = destination[1] as usize;

    let mut dist: Vec<Vec<i64>> = Vec::new();
    let mut i = 0;
    while i < m {
        let mut row: Vec<i64> = Vec::new();
        let mut j = 0;
        while j < n {
            row.push(-1);
            j += 1;
        }
        dist.push(row);
        i += 1;
    }

    let base: i64 = 1000000;
    let mut heap: Vec<i64> = Vec::new();

    dist[sr][sc] = 0;
    let start_code = (sr as i64) * n_i + (sc as i64);
    heap.push(start_code);

    while heap.len() > 0 {
        let packed = heap[0];
        let last_index = heap.len() - 1;
        let last_val = heap[last_index];
        heap.pop();
        if heap.len() > 0 {
            heap[0] = last_val;
            let mut idx: usize = 0;
            loop {
                let left = 2 * idx + 1;
                let right = 2 * idx + 2;
                let mut smallest = idx;
                if left < heap.len() && heap[left] < heap[smallest] {
                    smallest = left;
                }
                if right < heap.len() && heap[right] < heap[smallest] {
                    smallest = right;
                }
                if smallest != idx {
                    let tmp = heap[idx];
                    heap[idx] = heap[smallest];
                    heap[smallest] = tmp;
                    idx = smallest;
                } else {
                    break;
                }
            }
        }

        let d = packed / base;
        let code = packed % base;
        let r = (code / n_i) as usize;
        let c = (code % n_i) as usize;

        if dist[r][c] != d {
            continue;
        }

        if r == dr_dest && c == dc_dest {
            return d;
        }

        let mut k = 0;
        while k < 4 {
            let mut dr: i64 = 0;
            let mut dc: i64 = 0;
            if k == 0 {
                dr = -1;
            } else if k == 1 {
                dr = 1;
            } else if k == 2 {
                dc = -1;
            } else {
                dc = 1;
            }

            let stop = roll(maze, r, c, dr, dc, n);
            if stop != -1 {
                let nr = (stop / n_i) as usize;
                let nc = (stop % n_i) as usize;
                let mut steps: i64 = 0;
                if nr > r {
                    steps += nr as i64 - r as i64;
                } else {
                    steps += r as i64 - nr as i64;
                }
                if nc > c {
                    steps += nc as i64 - c as i64;
                } else {
                    steps += c as i64 - nc as i64;
                }
                let nd = d + steps;
                if dist[nr][nc] == -1 || nd < dist[nr][nc] {
                    dist[nr][nc] = nd;
                    let val = nd * base + stop;
                    heap.push(val);
                    let mut hi = heap.len() - 1;
                    while hi > 0 {
                        let parent = (hi - 1) / 2;
                        if heap[parent] > heap[hi] {
                            let tmp = heap[parent];
                            heap[parent] = heap[hi];
                            heap[hi] = tmp;
                            hi = parent;
                        } else {
                            break;
                        }
                    }
                }
            }
            k += 1;
        }
    }

    dist[dr_dest][dc_dest]
}

fn roll(maze: &[Vec<i64>], r: usize, c: usize, dr: i64, dc: i64, n: usize) -> i64 {
    let m = maze.len();
    let n_i = n as i64;
    let m_i = m as i64;
    let mut nr = r as i64;
    let mut nc = c as i64;
    let mut moved = false;

    loop {
        let tr = nr + dr;
        let tc = nc + dc;
        if tr < 0 || tr >= m_i || tc < 0 || tc >= n_i {
            break;
        }
        let tr_u = tr as usize;
        let tc_u = tc as usize;
        if maze[tr_u][tc_u] == 1 {
            break;
        }
        nr = tr;
        nc = tc;
        moved = true;
    }

    if !moved {
        return -1;
    }
    nr * n_i + nc
}
