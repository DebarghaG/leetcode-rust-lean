pub fn furthest_building(heights: &[i64], bricks: i64, ladders: i64) -> i64 {
    let n = heights.len();
    if n == 0 {
        return 0;
    }

    let mut heap: Vec<i64> = Vec::new();
    let mut heap_len: usize = 0;
    let mut remaining_bricks: i64 = bricks;

    let mut i: usize = 1;
    while i < n {
        let diff = heights[i] - heights[i - 1];

        if diff > 0 {
            if heap_len == heap.len() {
                heap.push(diff);
            } else {
                heap[heap_len] = diff;
            }
            heap_len += 1;

            let mut child: usize = heap_len - 1;
            while child > 0 {
                let parent: usize = (child - 1) / 2;
                if heap[parent] <= heap[child] {
                    break;
                }

                let temp = heap[parent];
                heap[parent] = heap[child];
                heap[child] = temp;
                child = parent;
            }

            if (heap_len as i64) > ladders {
                let min_value = heap[0];

                if heap_len == 1 {
                    heap_len = 0;
                } else {
                    let last_value = heap[heap_len - 1];
                    heap[0] = last_value;
                    heap_len -= 1;

                    let mut pos: usize = 0;
                    while pos < heap_len {
                        let left = pos * 2 + 1;
                        let right = left + 1;
                        let mut smallest = pos;

                        if left < heap_len && heap[left] < heap[smallest] {
                            smallest = left;
                        }
                        if right < heap_len && heap[right] < heap[smallest] {
                            smallest = right;
                        }
                        if smallest == pos {
                            break;
                        }

                        let temp = heap[pos];
                        heap[pos] = heap[smallest];
                        heap[smallest] = temp;
                        pos = smallest;
                    }
                }

                remaining_bricks -= min_value;
                if remaining_bricks < 0 {
                    return (i - 1) as i64;
                }
            }
        }

        i += 1;
    }

    (n as i64) - 1
}
