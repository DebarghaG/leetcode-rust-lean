pub fn min_operations(nums: &[i64], k: i64) -> i64 {
    let n: usize = nums.len();
    let mut heap: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        heap.push(nums[i]);
        i += 1;
    }

    // Build a min-heap in place.
    let mut start: usize = heap.len() / 2;
    while start > 0 {
        start -= 1;
        let mut idx: usize = start;
        let mut keep_going: bool = true;
        while keep_going {
            let left: usize = 2 * idx + 1;
            if left >= heap.len() {
                keep_going = false;
            } else {
                let mut smallest: usize = left;
                let right: usize = left + 1;
                if right < heap.len() && heap[right] < heap[left] {
                    smallest = right;
                }

                if heap[idx] <= heap[smallest] {
                    keep_going = false;
                } else {
                    let tmp: i64 = heap[idx];
                    heap[idx] = heap[smallest];
                    heap[smallest] = tmp;
                    idx = smallest;
                }
            }
        }
    }

    let mut ops: i64 = 0;
    let mut continue_loop: bool = true;

    while continue_loop {
        if heap.len() < 2 {
            continue_loop = false;
        } else if heap[0] >= k {
            continue_loop = false;
        } else {
            // Pop the minimum element x.
            let x: i64 = heap[0];
            let last_index: usize = heap.len() - 1;
            let last_value: i64 = heap[last_index];
            heap.pop();

            if heap.len() > 0 {
                heap[0] = last_value;
                let mut idx: usize = 0;
                let mut keep_going: bool = true;
                while keep_going {
                    let left: usize = 2 * idx + 1;
                    if left >= heap.len() {
                        keep_going = false;
                    } else {
                        let mut smallest: usize = left;
                        let right: usize = left + 1;
                        if right < heap.len() && heap[right] < heap[left] {
                            smallest = right;
                        }

                        if heap[idx] <= heap[smallest] {
                            keep_going = false;
                        } else {
                            let tmp: i64 = heap[idx];
                            heap[idx] = heap[smallest];
                            heap[smallest] = tmp;
                            idx = smallest;
                        }
                    }
                }
            }

            // Pop the second minimum element y.
            let y: i64 = heap[0];
            let last_index2: usize = heap.len() - 1;
            let last_value2: i64 = heap[last_index2];
            heap.pop();

            if heap.len() > 0 {
                heap[0] = last_value2;
                let mut idx: usize = 0;
                let mut keep_going: bool = true;
                while keep_going {
                    let left: usize = 2 * idx + 1;
                    if left >= heap.len() {
                        keep_going = false;
                    } else {
                        let mut smallest: usize = left;
                        let right: usize = left + 1;
                        if right < heap.len() && heap[right] < heap[left] {
                            smallest = right;
                        }

                        if heap[idx] <= heap[smallest] {
                            keep_going = false;
                        } else {
                            let tmp: i64 = heap[idx];
                            heap[idx] = heap[smallest];
                            heap[smallest] = tmp;
                            idx = smallest;
                        }
                    }
                }
            }

            // Insert min(x, y) * 2 + max(x, y).
            // Since x was popped first, x <= y.
            let new_value: i64 = 2 * x + y;
            heap.push(new_value);

            let mut idx: usize = heap.len() - 1;
            while idx > 0 {
                let parent: usize = (idx - 1) / 2;
                if heap[parent] <= heap[idx] {
                    idx = 0;
                } else {
                    let tmp: i64 = heap[parent];
                    heap[parent] = heap[idx];
                    heap[idx] = tmp;
                    idx = parent;
                }
            }

            ops += 1;
        }
    }

    ops
}
