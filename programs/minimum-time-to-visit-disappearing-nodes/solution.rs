fn heap_push(heap: &mut Vec<i64>, key: i64) {
    heap.push(key);
    let mut idx = heap.len() - 1;
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
}

fn heap_pop(heap: &mut Vec<i64>) -> i64 {
    let result = heap[0];
    let last = heap[heap.len() - 1];
    heap.pop();

    if heap.len() == 0 {
        return result;
    }

    heap[0] = last;
    let len = heap.len();
    let mut idx = 0;
    let mut done = false;

    while !done {
        let left = idx * 2 + 1;
        if left >= len {
            done = true;
        } else {
            let mut smallest = left;
            let right = left + 1;
            if right < len && heap[right] < heap[left] {
                smallest = right;
            }

            if heap[idx] <= heap[smallest] {
                done = true;
            } else {
                let tmp = heap[idx];
                heap[idx] = heap[smallest];
                heap[smallest] = tmp;
                idx = smallest;
            }
        }
    }

    result
}

pub fn minimum_time(n: i64, edges: &[Vec<i64>], disappear: &[i64]) -> Vec<i64> {
    let n_usize = n as usize;

    let mut head: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n_usize {
        head.push(-1);
        i += 1;
    }

    let m = edges.len();
    let mut to: Vec<i64> = Vec::new();
    let mut next: Vec<i64> = Vec::new();
    let mut weight: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < m {
        let u = edges[i][0];
        let v = edges[i][1];
        let w = edges[i][2];

        let idx1 = to.len() as i64;
        to.push(v);
        weight.push(w);
        next.push(head[u as usize]);
        head[u as usize] = idx1;

        let idx2 = to.len() as i64;
        to.push(u);
        weight.push(w);
        next.push(head[v as usize]);
        head[v as usize] = idx2;

        i += 1;
    }

    let inf: i64 = 1000000000000000000;
    let mut dist: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n_usize {
        dist.push(inf);
        i += 1;
    }

    dist[0] = 0;

    let base = n + 1;
    let mut heap: Vec<i64> = Vec::new();
    heap_push(&mut heap, 0);

    while heap.len() > 0 {
        let key = heap_pop(&mut heap);
        let d = key / base;
        let u = key % base;
        let uidx = u as usize;

        if d != dist[uidx] {
            continue;
        }

        if d >= disappear[uidx] {
            continue;
        }

        let mut e = head[uidx];
        while e != -1 {
            let vidx = to[e as usize] as usize;
            let w = weight[e as usize];
            let nd = d + w;

            if nd < disappear[vidx] && nd < dist[vidx] {
                dist[vidx] = nd;
                heap_push(&mut heap, nd * base + to[e as usize]);
            }

            e = next[e as usize];
        }
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n_usize {
        if dist[i] == inf {
            answer.push(-1);
        } else {
            answer.push(dist[i]);
        }
        i += 1;
    }

    answer
}
