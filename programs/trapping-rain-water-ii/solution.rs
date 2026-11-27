const BASE: i64 = 100000;

fn heap_push(heap: &mut Vec<i64>, len: usize, value: i64) -> usize {
    let mut idx = len;
    heap[idx] = value;

    while idx > 0 {
        let parent = (idx - 1) / 2;
        if heap[parent] <= heap[idx] {
            break;
        }
        let tmp = heap[parent];
        heap[parent] = heap[idx];
        heap[idx] = tmp;
        idx = parent;
    }

    len + 1
}

pub fn trap_rain_water(heightMap: &[Vec<i64>]) -> i64 {
    let m = heightMap.len();
    if m < 3 {
        return 0;
    }

    let n = heightMap[0].len();
    if n < 3 {
        return 0;
    }

    let total = m * n;

    let mut visited: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < total {
        visited.push(false);
        i += 1;
    }

    let mut heap: Vec<i64> = Vec::new();
    let mut z = 0;
    while z < total {
        heap.push(0);
        z += 1;
    }

    let mut heap_len: usize = 0;

    let mut c = 0;
    while c < n {
        let id_top = c;
        visited[id_top] = true;
        let h_top = heightMap[0][c];
        heap_len = heap_push(&mut heap, heap_len, h_top * BASE + id_top as i64);

        let id_bottom = (m - 1) * n + c;
        visited[id_bottom] = true;
        let h_bottom = heightMap[m - 1][c];
        heap_len = heap_push(&mut heap, heap_len, h_bottom * BASE + id_bottom as i64);

        c += 1;
    }

    let mut r = 1;
    while r < m - 1 {
        let id_left = r * n;
        visited[id_left] = true;
        let h_left = heightMap[r][0];
        heap_len = heap_push(&mut heap, heap_len, h_left * BASE + id_left as i64);

        let id_right = r * n + (n - 1);
        visited[id_right] = true;
        let h_right = heightMap[r][n - 1];
        heap_len = heap_push(&mut heap, heap_len, h_right * BASE + id_right as i64);

        r += 1;
    }

    let mut ans: i64 = 0;

    while heap_len > 0 {
        let enc = heap[0];
        heap_len -= 1;

        if heap_len > 0 {
            let last = heap[heap_len];
            heap[0] = last;

            let mut idx = 0;
            let mut done = false;

            while !done {
                let left = 2 * idx + 1;
                let right = 2 * idx + 2;
                let mut smallest = idx;

                if left < heap_len && heap[left] < heap[smallest] {
                    smallest = left;
                }
                if right < heap_len && heap[right] < heap[smallest] {
                    smallest = right;
                }

                if smallest == idx {
                    done = true;
                } else {
                    let tmp = heap[smallest];
                    heap[smallest] = heap[idx];
                    heap[idx] = tmp;
                    idx = smallest;
                }
            }
        }

        let level = enc / BASE;
        let id = (enc % BASE) as usize;
        let r = id / n;
        let c = id % n;

        if r > 0 {
            let nr = r - 1;
            let nid = nr * n + c;
            if !visited[nid] {
                visited[nid] = true;
                let h = heightMap[nr][c];
                let water = if level > h { level } else { h };
                ans += water - h;
                heap_len = heap_push(&mut heap, heap_len, water * BASE + nid as i64);
            }
        }

        if r + 1 < m {
            let nr = r + 1;
            let nid = nr * n + c;
            if !visited[nid] {
                visited[nid] = true;
                let h = heightMap[nr][c];
                let water = if level > h { level } else { h };
                ans += water - h;
                heap_len = heap_push(&mut heap, heap_len, water * BASE + nid as i64);
            }
        }

        if c > 0 {
            let nc = c - 1;
            let nid = r * n + nc;
            if !visited[nid] {
                visited[nid] = true;
                let h = heightMap[r][nc];
                let water = if level > h { level } else { h };
                ans += water - h;
                heap_len = heap_push(&mut heap, heap_len, water * BASE + nid as i64);
            }
        }

        if c + 1 < n {
            let nc = c + 1;
            let nid = r * n + nc;
            if !visited[nid] {
                visited[nid] = true;
                let h = heightMap[r][nc];
                let water = if level > h { level } else { h };
                ans += water - h;
                heap_len = heap_push(&mut heap, heap_len, water * BASE + nid as i64);
            }
        }
    }

    ans
}
