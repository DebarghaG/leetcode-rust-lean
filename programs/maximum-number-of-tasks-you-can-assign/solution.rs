fn st_add(tree: &mut [i64], size: usize, pos: usize, delta: i64) {
    let mut p = pos + size;
    tree[p] = tree[p] + delta;
    p = p / 2;
    while p > 0 {
        tree[p] = tree[2 * p] + tree[2 * p + 1];
        p = p / 2;
    }
}

fn st_prefix(tree: &[i64], size: usize, end: usize) -> i64 {
    let mut l = size;
    let mut r = size + end;
    let mut sum = 0;
    while l < r {
        if l % 2 == 1 {
            sum = sum + tree[l];
            l = l + 1;
        }
        if r % 2 == 1 {
            r = r - 1;
            sum = sum + tree[r];
        }
        l = l / 2;
        r = r / 2;
    }
    sum
}

fn st_kth(tree: &[i64], size: usize, rank: i64) -> usize {
    let mut node = 1;
    let mut r = rank;
    while node < size {
        let left = 2 * node;
        if tree[left] >= r {
            node = left;
        } else {
            r = r - tree[left];
            node = left + 1;
        }
    }
    node - size
}

fn can_assign(tasks: &[i64], workers: &[i64], k: usize, mut pills: i64, strength: i64) -> bool {
    if k == 0 {
        return true;
    }
    if k > tasks.len() || k > workers.len() {
        return false;
    }

    let m = workers.len();
    let offset = m - k;

    let mut size = 1;
    while size < k {
        size = size * 2;
    }

    let mut tree: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < 2 * size {
        tree.push(0);
        i += 1;
    }

    i = 0;
    while i < k {
        tree[size + i] = 1;
        i += 1;
    }

    let mut p = size;
    while p > 1 {
        p -= 1;
        tree[p] = tree[2 * p] + tree[2 * p + 1];
    }

    let mut ti = k;
    while ti > 0 {
        ti -= 1;
        let task = tasks[ti];
        let total = tree[1];
        if total <= 0 {
            return false;
        }

        let max_idx = st_kth(&tree, size, total);
        if workers[offset + max_idx] >= task {
            st_add(&mut tree, size, max_idx, -1);
        } else {
            if pills <= 0 {
                return false;
            }

            let threshold = task - strength;
            let mut lo = 0;
            let mut hi = k;
            while lo < hi {
                let mid = (lo + hi) / 2;
                if workers[offset + mid] >= threshold {
                    hi = mid;
                } else {
                    lo = mid + 1;
                }
            }

            let lb = lo;
            if lb >= k {
                return false;
            }

            let before = st_prefix(&tree, size, lb);
            let total2 = tree[1];
            if before >= total2 {
                return false;
            }

            let rank = before + 1;
            let idx = st_kth(&tree, size, rank);
            st_add(&mut tree, size, idx, -1);
            pills -= 1;
        }
    }

    true
}

pub fn max_task_assign(tasks: &[i64], workers: &[i64], pills: i64, strength: i64) -> i64 {
    let n = tasks.len();
    let m = workers.len();

    let mut ts: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        ts.push(tasks[i]);
        i += 1;
    }
    ts.sort();

    let mut ws: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        ws.push(workers[i]);
        i += 1;
    }
    ws.sort();

    let mut max_k = n;
    if m < max_k {
        max_k = m;
    }

    let mut low: usize = 0;
    let mut high: usize = max_k;
    let mut ans: usize = 0;

    while low <= high {
        let mid = (low + high) / 2;
        if can_assign(&ts, &ws, mid, pills, strength) {
            ans = mid;
            low = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            high = mid - 1;
        }
    }

    ans as i64
}
