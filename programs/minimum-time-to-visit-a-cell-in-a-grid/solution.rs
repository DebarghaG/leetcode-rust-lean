fn heap_push(h_idx: &mut Vec<usize>, h_key: &mut Vec<i64>, idx: usize, key: i64) {
    h_idx.push(idx);
    h_key.push(key);

    let mut i = h_idx.len() - 1;
    while i > 0 {
        let parent = (i - 1) / 2;
        if h_key[parent] <= h_key[i] {
            break;
        }

        let tmp_idx = h_idx[parent];
        h_idx[parent] = h_idx[i];
        h_idx[i] = tmp_idx;

        let tmp_key = h_key[parent];
        h_key[parent] = h_key[i];
        h_key[i] = tmp_key;

        i = parent;
    }
}

fn try_relax(
    cur_time: i64,
    ni: usize,
    required: i64,
    dist: &mut Vec<i64>,
    h_idx: &mut Vec<usize>,
    h_key: &mut Vec<i64>,
) {
    let mut next_time = cur_time + 1;

    if next_time < required {
        next_time = required;
    }

    if (next_time - cur_time) % 2 == 0 {
        next_time += 1;
    }

    if next_time < dist[ni] {
        dist[ni] = next_time;
        heap_push(h_idx, h_key, ni, next_time);
    }
}

pub fn minimum_time(grid: &[Vec<i64>]) -> i64 {
    let m = grid.len();
    let n = grid[0].len();

    if grid[0][1] > 1 && grid[1][0] > 1 {
        return -1;
    }

    let total = m * n;
    let inf: i64 = 1_000_000_000_000_000_000;

    let mut dist: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < total {
        dist.push(inf);
        i += 1;
    }
    dist[0] = 0;

    let mut h_idx: Vec<usize> = Vec::new();
    let mut h_key: Vec<i64> = Vec::new();
    heap_push(&mut h_idx, &mut h_key, 0, 0);

    let target = total - 1;

    while h_idx.len() > 0 {
        let cur_idx = h_idx[0];
        let cur_time = h_key[0];

        let last = h_idx.len() - 1;
        h_idx[0] = h_idx[last];
        h_key[0] = h_key[last];
        h_idx.pop();
        h_key.pop();

        if h_idx.len() > 0 {
            let len = h_idx.len();
            let mut pos = 0;

            while pos < len {
                let left = pos * 2 + 1;
                if left >= len {
                    break;
                }

                let mut smallest = pos;

                if h_key[left] < h_key[smallest] {
                    smallest = left;
                }

                let right = left + 1;
                if right < len && h_key[right] < h_key[smallest] {
                    smallest = right;
                }

                if smallest == pos {
                    break;
                }

                let tmp_idx = h_idx[pos];
                h_idx[pos] = h_idx[smallest];
                h_idx[smallest] = tmp_idx;

                let tmp_key = h_key[pos];
                h_key[pos] = h_key[smallest];
                h_key[smallest] = tmp_key;

                pos = smallest;
            }
        }

        if cur_time != dist[cur_idx] {
            continue;
        }

        if cur_idx == target {
            return cur_time;
        }

        let r = cur_idx / n;
        let c = cur_idx % n;

        if r > 0 {
            let ni = (r - 1) * n + c;
            let required = grid[r - 1][c];
            try_relax(cur_time, ni, required, &mut dist, &mut h_idx, &mut h_key);
        }

        if r + 1 < m {
            let ni = (r + 1) * n + c;
            let required = grid[r + 1][c];
            try_relax(cur_time, ni, required, &mut dist, &mut h_idx, &mut h_key);
        }

        if c > 0 {
            let ni = r * n + (c - 1);
            let required = grid[r][c - 1];
            try_relax(cur_time, ni, required, &mut dist, &mut h_idx, &mut h_key);
        }

        if c + 1 < n {
            let ni = r * n + (c + 1);
            let required = grid[r][c + 1];
            try_relax(cur_time, ni, required, &mut dist, &mut h_idx, &mut h_key);
        }
    }

    let answer = dist[target];
    if answer == inf {
        -1
    } else {
        answer
    }
}
