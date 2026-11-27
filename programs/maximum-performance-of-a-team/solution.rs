fn sort_by_efficiency_desc(order: &mut Vec<i64>, efficiency: &[i64]) {
    let n = order.len();
    if n == 0 {
        return;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < n {
        temp.push(0);
        p += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = left + width + width;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;
            let mut t = left;

            while i < mid && j < right {
                let ii = order[i] as usize;
                let jj = order[j] as usize;

                if efficiency[jj] > efficiency[ii] {
                    temp[t] = order[j];
                    j += 1;
                } else {
                    temp[t] = order[i];
                    i += 1;
                }
                t += 1;
            }

            while i < mid {
                temp[t] = order[i];
                i += 1;
                t += 1;
            }

            while j < right {
                temp[t] = order[j];
                j += 1;
                t += 1;
            }

            left = right;
        }

        let mut c: usize = 0;
        while c < n {
            order[c] = temp[c];
            c += 1;
        }

        width = width * 2;
    }
}

fn heap_push(heap: &mut Vec<i64>, x: i64) {
    heap.push(x);
    let mut idx = heap.len() - 1;

    while idx > 0 {
        let parent = (idx - 1) / 2;

        if heap[parent] > heap[idx] {
            let tmp = heap[parent];
            heap[parent] = heap[idx];
            heap[idx] = tmp;
            idx = parent;
        } else {
            break;
        }
    }
}

fn heap_pop(heap: &mut Vec<i64>) -> i64 {
    let n = heap.len();
    let root = heap[0];

    if n == 1 {
        heap.pop();
        return root;
    }

    heap[0] = heap[n - 1];
    heap.pop();

    let len = heap.len();
    let mut idx: usize = 0;

    while idx < len {
        let left = 2 * idx + 1;
        let right = left + 1;
        let mut smallest = idx;

        if left < len && heap[left] < heap[smallest] {
            smallest = left;
        }

        if right < len && heap[right] < heap[smallest] {
            smallest = right;
        }

        if smallest == idx {
            break;
        }

        let tmp = heap[idx];
        heap[idx] = heap[smallest];
        heap[smallest] = tmp;
        idx = smallest;
    }

    root
}

pub fn max_performance(n: i64, speed: &[i64], efficiency: &[i64], k: i64) -> i64 {
    let len = speed.len();

    let mut order: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < len {
        order.push(i as i64);
        i += 1;
    }

    sort_by_efficiency_desc(&mut order, efficiency);

    let mut heap: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut best: i64 = 0;

    let mut idx: usize = 0;
    while idx < len {
        let pos = order[idx] as usize;
        let sp = speed[pos];
        let ef = efficiency[pos];

        heap_push(&mut heap, sp);
        sum += sp;

        if heap.len() as i64 > k {
            let removed = heap_pop(&mut heap);
            sum -= removed;
        }

        let performance = sum * ef;
        if performance > best {
            best = performance;
        }

        idx += 1;
    }

    best % 1000000007
}
