fn interval_len(intervals: &[Vec<i64>], idx: usize) -> i64 {
    intervals[idx][1] - intervals[idx][0] + 1
}

fn interval_less(intervals: &[Vec<i64>], a: usize, b: usize) -> bool {
    interval_len(intervals, a) < interval_len(intervals, b)
}

fn heap_push(intervals: &[Vec<i64>], heap: &mut Vec<usize>, x: usize) {
    heap.push(x);
    let mut child = heap.len() - 1;

    while child > 0 {
        let parent = (child - 1) / 2;
        let child_val = heap[child];
        let parent_val = heap[parent];

        if interval_less(intervals, child_val, parent_val) {
            heap[child] = parent_val;
            heap[parent] = child_val;
            child = parent;
        } else {
            break;
        }
    }
}

fn heap_pop(intervals: &[Vec<i64>], heap: &mut Vec<usize>) {
    let n = heap.len();
    if n == 0 {
        return;
    }

    let last = heap[n - 1];
    heap.pop();

    if heap.len() == 0 {
        return;
    }

    heap[0] = last;
    let mut parent: usize = 0;

    while parent < heap.len() {
        let left = 2 * parent + 1;
        if left >= heap.len() {
            break;
        }

        let right = left + 1;
        let mut smallest = left;

        if right < heap.len() {
            if interval_less(intervals, heap[right], heap[left]) {
                smallest = right;
            }
        }

        if interval_less(intervals, heap[smallest], heap[parent]) {
            let tmp = heap[parent];
            heap[parent] = heap[smallest];
            heap[smallest] = tmp;
            parent = smallest;
        } else {
            break;
        }
    }
}

fn sort_interval_order(
    intervals: &[Vec<i64>],
    order: &mut Vec<usize>,
    temp: &mut Vec<usize>,
) {
    let n = order.len();
    let mut width: usize = 1;

    while width < n {
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };

            let end = if start + 2 * width < n {
                start + 2 * width
            } else {
                n
            };

            let mut a = start;
            let mut b = mid;
            let mut k = start;

            while a < mid && b < end {
                let ia = order[a];
                let ib = order[b];

                if intervals[ia][0] <= intervals[ib][0] {
                    temp[k] = ia;
                    a += 1;
                } else {
                    temp[k] = ib;
                    b += 1;
                }

                k += 1;
            }

            while a < mid {
                temp[k] = order[a];
                a += 1;
                k += 1;
            }

            while b < end {
                temp[k] = order[b];
                b += 1;
                k += 1;
            }

            start += 2 * width;
        }

        let mut i: usize = 0;
        while i < n {
            order[i] = temp[i];
            i += 1;
        }

        width *= 2;
    }
}

fn sort_query_order(queries: &[i64], order: &mut Vec<usize>, temp: &mut Vec<usize>) {
    let n = order.len();
    let mut width: usize = 1;

    while width < n {
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };

            let end = if start + 2 * width < n {
                start + 2 * width
            } else {
                n
            };

            let mut a = start;
            let mut b = mid;
            let mut k = start;

            while a < mid && b < end {
                let ia = order[a];
                let ib = order[b];

                if queries[ia] <= queries[ib] {
                    temp[k] = ia;
                    a += 1;
                } else {
                    temp[k] = ib;
                    b += 1;
                }

                k += 1;
            }

            while a < mid {
                temp[k] = order[a];
                a += 1;
                k += 1;
            }

            while b < end {
                temp[k] = order[b];
                b += 1;
                k += 1;
            }

            start += 2 * width;
        }

        let mut i: usize = 0;
        while i < n {
            order[i] = temp[i];
            i += 1;
        }

        width *= 2;
    }
}

pub fn min_interval(intervals: &[Vec<i64>], queries: &[i64]) -> Vec<i64> {
    let n = intervals.len();
    let m = queries.len();

    let mut order: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        order.push(i);
        i += 1;
    }

    let mut temp_order: Vec<usize> = Vec::new();
    i = 0;
    while i < n {
        temp_order.push(0);
        i += 1;
    }

    sort_interval_order(intervals, &mut order, &mut temp_order);

    let mut qorder: Vec<usize> = Vec::new();
    i = 0;
    while i < m {
        qorder.push(i);
        i += 1;
    }

    let mut qtemp: Vec<usize> = Vec::new();
    i = 0;
    while i < m {
        qtemp.push(0);
        i += 1;
    }

    sort_query_order(queries, &mut qorder, &mut qtemp);

    let mut ans: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        ans.push(-1);
        i += 1;
    }

    let mut heap: Vec<usize> = Vec::new();
    let mut ptr: usize = 0;
    let mut qi: usize = 0;

    while qi < m {
        let qpos = qorder[qi];
        let q = queries[qpos];

        while ptr < n {
            let interval_idx = order[ptr];

            if intervals[interval_idx][0] <= q {
                heap_push(intervals, &mut heap, interval_idx);
                ptr += 1;
            } else {
                break;
            }
        }

        while heap.len() > 0 {
            let top = heap[0];

            if intervals[top][1] < q {
                heap_pop(intervals, &mut heap);
            } else {
                break;
            }
        }

        if heap.len() > 0 {
            let top = heap[0];
            ans[qpos] = interval_len(intervals, top);
        } else {
            ans[qpos] = -1;
        }

        qi += 1;
    }

    ans
}
