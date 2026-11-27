pub fn results_array(queries: &[Vec<i64>], k: i64) -> Vec<i64> {
    let n = queries.len();
    let kk: usize = k as usize;
    let mut res: Vec<i64> = Vec::new();
    let mut heap: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let x = queries[i][0];
        let y = queries[i][1];

        let ax = if x < 0 { -x } else { x };
        let ay = if y < 0 { -y } else { y };
        let dist = ax + ay;

        if heap.len() < kk {
            heap.push(dist);

            let mut idx = heap.len() - 1;
            let mut keep_going = true;
            while keep_going {
                if idx == 0 {
                    keep_going = false;
                } else {
                    let parent = (idx - 1) / 2;
                    if heap[idx] > heap[parent] {
                        let tmp = heap[idx];
                        heap[idx] = heap[parent];
                        heap[parent] = tmp;
                        idx = parent;
                    } else {
                        keep_going = false;
                    }
                }
            }
        } else {
            if dist < heap[0] {
                heap[0] = dist;

                let len = heap.len();
                let mut idx: usize = 0;
                let mut keep_going = true;
                while keep_going {
                    let left = 2 * idx + 1;
                    let right = left + 1;
                    let mut largest = idx;

                    if left < len && heap[left] > heap[largest] {
                        largest = left;
                    }
                    if right < len && heap[right] > heap[largest] {
                        largest = right;
                    }

                    if largest != idx {
                        let tmp = heap[idx];
                        heap[idx] = heap[largest];
                        heap[largest] = tmp;
                        idx = largest;
                    } else {
                        keep_going = false;
                    }
                }
            }
        }

        if heap.len() < kk {
            res.push(-1);
        } else {
            res.push(heap[0]);
        }

        i += 1;
    }

    res
}
