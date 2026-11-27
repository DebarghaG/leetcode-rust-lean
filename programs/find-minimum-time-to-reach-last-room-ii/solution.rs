fn heap_push(keys: &mut Vec<i64>, ids: &mut Vec<usize>, key: i64, id: usize) {
    let mut i = keys.len();
    keys.push(key);
    ids.push(id);

    while i > 0 {
        let p = (i - 1) / 2;
        if keys[p] <= keys[i] {
            break;
        }

        keys.swap(p, i);
        ids.swap(p, i);
        i = p;
    }
}

fn heap_pop(keys: &mut Vec<i64>, ids: &mut Vec<usize>) -> usize {
    let n = keys.len();
    let top = ids[0];

    keys.swap(0, n - 1);
    ids.swap(0, n - 1);

    keys.pop();
    ids.pop();

    let len = n - 1;
    if len > 0 {
        let mut i = 0;
        while i < len {
            let left = i * 2 + 1;
            if left >= len {
                break;
            }

            let right = left + 1;
            let mut smallest = left;
            if right < len && keys[right] < keys[left] {
                smallest = right;
            }

            if keys[i] <= keys[smallest] {
                break;
            }

            keys.swap(i, smallest);
            ids.swap(i, smallest);
            i = smallest;
        }
    }

    top
}

pub fn min_time_to_reach(moveTime: &[Vec<i64>]) -> i64 {
    let n = moveTime.len();
    let m = moveTime[0].len();
    let total = n * m;
    let dest = total - 1;

    let mut visited: Vec<bool> = Vec::new();

    let mut i = 0;
    while i < total {
        visited.push(false);
        i += 1;
    }

    i = 0;
    while i < total {
        visited.push(true);
        i += 1;
    }

    let mut heap_keys: Vec<i64> = Vec::new();
    let mut heap_ids: Vec<usize> = Vec::new();

    heap_push(&mut heap_keys, &mut heap_ids, 0, 0);

    let mut visited_count: usize = 0;

    while heap_keys.len() > 0 {
        let cur = heap_keys[0];
        let id = heap_pop(&mut heap_keys, &mut heap_ids);

        if visited[id] == false {
            let supply = total + visited_count;
            visited.swap(id, supply);
            visited_count += 1;

            if id == dest {
                return cur;
            }

            let r = id / m;
            let c = id % m;

            if r > 0 {
                let nr = r - 1;
                let nc = c;
                let nid = nr * m + nc;

                if visited[nid] == false {
                    let mt = moveTime[nr][nc];
                    let start = if cur > mt { cur } else { mt };
                    let parity = (nr + nc) % 2;
                    let cost: i64 = if parity == 1 { 1 } else { 2 };
                    let nd = start + cost;
                    heap_push(&mut heap_keys, &mut heap_ids, nd, nid);
                }
            }

            if r + 1 < n {
                let nr = r + 1;
                let nc = c;
                let nid = nr * m + nc;

                if visited[nid] == false {
                    let mt = moveTime[nr][nc];
                    let start = if cur > mt { cur } else { mt };
                    let parity = (nr + nc) % 2;
                    let cost: i64 = if parity == 1 { 1 } else { 2 };
                    let nd = start + cost;
                    heap_push(&mut heap_keys, &mut heap_ids, nd, nid);
                }
            }

            if c > 0 {
                let nr = r;
                let nc = c - 1;
                let nid = nr * m + nc;

                if visited[nid] == false {
                    let mt = moveTime[nr][nc];
                    let start = if cur > mt { cur } else { mt };
                    let parity = (nr + nc) % 2;
                    let cost: i64 = if parity == 1 { 1 } else { 2 };
                    let nd = start + cost;
                    heap_push(&mut heap_keys, &mut heap_ids, nd, nid);
                }
            }

            if c + 1 < m {
                let nr = r;
                let nc = c + 1;
                let nid = nr * m + nc;

                if visited[nid] == false {
                    let mt = moveTime[nr][nc];
                    let start = if cur > mt { cur } else { mt };
                    let parity = (nr + nc) % 2;
                    let cost: i64 = if parity == 1 { 1 } else { 2 };
                    let nd = start + cost;
                    heap_push(&mut heap_keys, &mut heap_ids, nd, nid);
                }
            }
        }
    }

    0
}
