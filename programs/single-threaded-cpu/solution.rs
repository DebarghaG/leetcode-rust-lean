fn idx_less(tasks: &[Vec<i64>], a: i64, b: i64) -> bool {
    let ai = a as usize;
    let bi = b as usize;
    let ea = tasks[ai][0];
    let eb = tasks[bi][0];
    if ea < eb {
        true
    } else if ea > eb {
        false
    } else {
        a < b
    }
}

fn sort_by_enqueue(tasks: &[Vec<i64>], arr: &mut Vec<i64>) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mut mid = start + width;
            if mid > n {
                mid = n;
            }

            let mut end = start + width * 2;
            if end > n {
                end = n;
            }

            let mut i = start;
            let mut j = mid;

            while i < mid && j < end {
                if idx_less(tasks, arr[j], arr[i]) {
                    merged.push(arr[j]);
                    j += 1;
                } else {
                    merged.push(arr[i]);
                    i += 1;
                }
            }

            while i < mid {
                merged.push(arr[i]);
                i += 1;
            }

            while j < end {
                merged.push(arr[j]);
                j += 1;
            }

            start = end;
        }

        let mut k: usize = 0;
        while k < n {
            arr[k] = merged[k];
            k += 1;
        }

        width = width * 2;
    }
}

fn task_less(tasks: &[Vec<i64>], a: i64, b: i64) -> bool {
    let ai = a as usize;
    let bi = b as usize;
    let pa = tasks[ai][1];
    let pb = tasks[bi][1];

    if pa < pb {
        true
    } else if pa > pb {
        false
    } else {
        a < b
    }
}

fn heap_push(tasks: &[Vec<i64>], heap: &mut Vec<i64>, idx: i64) {
    heap.push(idx);
    let mut i: usize = heap.len() - 1;

    while i > 0 {
        let parent: usize = (i - 1) / 2;

        if task_less(tasks, heap[i], heap[parent]) {
            let tmp: i64 = heap[i];
            heap[i] = heap[parent];
            heap[parent] = tmp;
            i = parent;
        } else {
            break;
        }
    }
}

fn heap_pop(tasks: &[Vec<i64>], heap: &mut Vec<i64>) -> i64 {
    let n = heap.len();
    let top = heap[0];
    let last = heap[n - 1];

    heap.pop();

    let m = heap.len();
    if m == 0 {
        return top;
    }

    heap[0] = last;

    let mut i: usize = 0;
    loop {
        let left: usize = 2 * i + 1;
        let right: usize = 2 * i + 2;
        let mut smallest: usize = i;

        if left < m && task_less(tasks, heap[left], heap[smallest]) {
            smallest = left;
        }

        if right < m && task_less(tasks, heap[right], heap[smallest]) {
            smallest = right;
        }

        if smallest == i {
            break;
        }

        let tmp: i64 = heap[i];
        heap[i] = heap[smallest];
        heap[smallest] = tmp;
        i = smallest;
    }

    top
}

pub fn get_order(tasks: &[Vec<i64>]) -> Vec<i64> {
    let n = tasks.len();
    let mut result: Vec<i64> = Vec::new();

    if n == 0 {
        return result;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        order.push(i as i64);
        i += 1;
    }

    sort_by_enqueue(tasks, &mut order);

    let mut heap: Vec<i64> = Vec::new();
    let mut next: usize = 0;
    let mut time: i64 = 0;

    while result.len() < n {
        if heap.len() == 0 {
            if next < n {
                time = tasks[order[next] as usize][0];

                while next < n && tasks[order[next] as usize][0] <= time {
                    heap_push(tasks, &mut heap, order[next]);
                    next += 1;
                }
            }
        } else {
            let id = heap_pop(tasks, &mut heap);
            result.push(id);

            time = time + tasks[id as usize][1];

            while next < n && tasks[order[next] as usize][0] <= time {
                heap_push(tasks, &mut heap, order[next]);
                next += 1;
            }
        }
    }

    result
}
