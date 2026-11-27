#[derive(Debug)]
pub struct RankedItems(pub Vec<Vec<i64>>);

impl RankedItems {
    pub fn len(&self) -> usize {
        self.0.len()
    }
}

impl core::ops::Index<usize> for RankedItems {
    type Output = Vec<i64>;
    fn index(&self, index: usize) -> &Vec<i64> {
        &self.0[index]
    }
}

impl PartialEq<Vec<Vec<i64>>> for RankedItems {
    fn eq(&self, other: &Vec<Vec<i64>>) -> bool {
        let na = self.0.len();
        let nb = other.len();
        let mut ok: bool = na == nb;
        let mut i: usize = 0;
        while ok && i < na {
            if self.0[i].len() != other[i].len() {
                ok = false;
            }
            let mut j: usize = 0;
            while ok && j < self.0[i].len() {
                if self.0[i][j] != other[i][j] {
                    ok = false;
                }
                j += 1;
            }
            i += 1;
        }
        ok
    }
}

pub fn highest_ranked_k_items(
    grid: &[Vec<i64>],
    pricing: &[i64],
    start: &[i64],
    k: i64,
) -> RankedItems {
    let mut out: Vec<Vec<i64>> = Vec::new();

    let m = grid.len();
    if m == 0 {
        return RankedItems(out);
    }
    let n = grid[0].len();
    if n == 0 {
        return RankedItems(out);
    }
    if pricing.len() < 2 || start.len() < 2 {
        return RankedItems(out);
    }

    let low = pricing[0];
    let high = pricing[1];

    if start[0] < 0 || start[1] < 0 {
        return RankedItems(out);
    }
    let sr = start[0] as usize;
    let sc = start[1] as usize;
    if sr >= m || sc >= n {
        return RankedItems(out);
    }

    let cells = m * n;
    let cells_i = cells as i64;
    let n_i = n as i64;

    let mut visited: Vec<bool> = Vec::new();
    let mut t = 0usize;
    while t < cells {
        visited.push(false);
        t += 1;
    }

    let mut queue: Vec<usize> = Vec::new();
    let seed = sr * n + sc;
    visited[seed] = true;
    queue.push(seed);

    let mut head = 0usize;
    let mut dist: i64 = 0;
    let base: i64 = 100001;
    let mut keys: Vec<i64> = Vec::new();

    while head < queue.len() {
        let layer_end = queue.len();
        while head < layer_end {
            let idx = queue[head];
            head += 1;

            let r = idx / n;
            let c = idx % n;
            let val = grid[r][c];

            if val >= low && val <= high {
                let rc = (r as i64) * n_i + (c as i64);
                let key = (dist * base + val) * cells_i + rc;
                keys.push(key);
            }

            if r > 0 {
                let nr = r - 1;
                let ni = nr * n + c;
                if !visited[ni] && grid[nr][c] != 0 {
                    visited[ni] = true;
                    queue.push(ni);
                }
            }
            if r + 1 < m {
                let nr = r + 1;
                let ni = nr * n + c;
                if !visited[ni] && grid[nr][c] != 0 {
                    visited[ni] = true;
                    queue.push(ni);
                }
            }
            if c > 0 {
                let nc = c - 1;
                let ni = r * n + nc;
                if !visited[ni] && grid[r][nc] != 0 {
                    visited[ni] = true;
                    queue.push(ni);
                }
            }
            if c + 1 < n {
                let nc = c + 1;
                let ni = r * n + nc;
                if !visited[ni] && grid[r][nc] != 0 {
                    visited[ni] = true;
                    queue.push(ni);
                }
            }
        }
        dist += 1;
    }

    heap_sort(&mut keys);

    let mut take = keys.len();
    if k <= 0 {
        take = 0;
    } else {
        let kk = k as usize;
        if kk < take {
            take = kk;
        }
    }

    let mut p = 0usize;
    while p < take {
        let rc = keys[p] % cells_i;

        let mut pair: Vec<i64> = Vec::new();
        pair.push(rc / n_i);
        pair.push(rc % n_i);
        out.push(pair);

        p += 1;
    }

    RankedItems(out)
}

fn heap_sort(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut i = n / 2;
    while i > 0 {
        i -= 1;
        sift_down(v, i, n);
    }

    let mut end = n;
    while end > 1 {
        let tmp = v[0];
        v[0] = v[end - 1];
        v[end - 1] = tmp;

        end -= 1;
        sift_down(v, 0, end);
    }
}

fn sift_down(v: &mut Vec<i64>, start: usize, n: usize) {
    let mut i = start;
    loop {
        let mut largest = i;
        let left = 2 * i + 1;
        let right = 2 * i + 2;

        if left < n && v[left] > v[largest] {
            largest = left;
        }
        if right < n && v[right] > v[largest] {
            largest = right;
        }
        if largest == i {
            break;
        }

        let tmp = v[i];
        v[i] = v[largest];
        v[largest] = tmp;

        i = largest;
    }
}
