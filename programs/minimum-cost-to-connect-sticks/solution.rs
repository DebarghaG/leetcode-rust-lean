pub fn connect_sticks(sticks: &[i64]) -> i64 {
    let n = sticks.len();
    if n <= 1 {
        return 0;
    }

    let mut heap: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < n {
        heap.push(sticks[k]);
        k += 1;
    }

    // Build a min-heap in place.
    let mut start: usize = n / 2;
    while start > 0 {
        start -= 1;
        let mut idx = start;
        let mut active = true;
        while active {
            let left = 2 * idx + 1;
            if left >= n {
                active = false;
            } else {
                let mut smallest = left;
                let right = left + 1;
                if right < n && heap[right] < heap[left] {
                    smallest = right;
                }
                if heap[smallest] < heap[idx] {
                    let tmp = heap[idx];
                    heap[idx] = heap[smallest];
                    heap[smallest] = tmp;
                    idx = smallest;
                } else {
                    active = false;
                }
            }
        }
    }

    let mut len = n;
    let mut total: i64 = 0;
    let mut step: usize = 0;

    while step < n - 1 {
        // Extract the smallest element.
        let first = heap[0];
        len -= 1;
        if len > 0 {
            heap[0] = heap[len];
            let mut idx = 0;
            let mut active = true;
            while active {
                let left = 2 * idx + 1;
                if left >= len {
                    active = false;
                } else {
                    let mut smallest = left;
                    let right = left + 1;
                    if right < len && heap[right] < heap[left] {
                        smallest = right;
                    }
                    if heap[smallest] < heap[idx] {
                        let tmp = heap[idx];
                        heap[idx] = heap[smallest];
                        heap[smallest] = tmp;
                        idx = smallest;
                    } else {
                        active = false;
                    }
                }
            }
        }

        // Extract the second smallest element.
        let second = heap[0];
        len -= 1;
        if len > 0 {
            heap[0] = heap[len];
            let mut idx = 0;
            let mut active = true;
            while active {
                let left = 2 * idx + 1;
                if left >= len {
                    active = false;
                } else {
                    let mut smallest = left;
                    let right = left + 1;
                    if right < len && heap[right] < heap[left] {
                        smallest = right;
                    }
                    if heap[smallest] < heap[idx] {
                        let tmp = heap[idx];
                        heap[idx] = heap[smallest];
                        heap[smallest] = tmp;
                        idx = smallest;
                    } else {
                        active = false;
                    }
                }
            }
        }

        let combined = first + second;
        total += combined;

        // Insert the combined stick.
        if len < heap.len() {
            heap[len] = combined;
        } else {
            heap.push(combined);
        }

        let mut idx = len;
        len += 1;
        let mut active = true;
        while active && idx > 0 {
            let parent = (idx - 1) / 2;
            if heap[idx] < heap[parent] {
                let tmp = heap[idx];
                heap[idx] = heap[parent];
                heap[parent] = tmp;
                idx = parent;
            } else {
                active = false;
            }
        }

        step += 1;
    }

    total
}
