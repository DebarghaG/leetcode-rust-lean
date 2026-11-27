pub fn get_skyline(buildings: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = buildings.len();
    let base: i64 = 1048576;
    let half: i64 = 524288;

    let mut events: Vec<i64> = Vec::new();
    let mut active: Vec<bool> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let left = buildings[i][0];
        let right = buildings[i][1];
        let id = i as i64;

        // start event: type 0, encoded as id
        events.push(left * base + id);
        // end event: type 1, encoded as half + id
        events.push(right * base + half + id);

        active.push(true);
        i += 1;
    }

    events.sort();

    let mut heap: Vec<i64> = Vec::new();
    let mut res: Vec<Vec<i64>> = Vec::new();
    let mut last_h: i64 = 0;

    let mut idx: usize = 0;
    let m = events.len();

    while idx < m {
        let x = events[idx] / base;

        while idx < m && events[idx] / base == x {
            let key = events[idx];
            let rem = key % base;

            if rem >= half {
                // end event
                let id = rem - half;
                let id_u = id as usize;
                active[id_u] = false;
            } else {
                // start event
                let id = rem;
                let id_u = id as usize;
                let h = buildings[id_u][2];

                let hkey = h * base + id;
                heap.push(hkey);

                let mut pos = heap.len() - 1;
                while pos > 0 {
                    let parent = (pos - 1) / 2;
                    if heap[parent] < heap[pos] {
                        let tmp = heap[parent];
                        heap[parent] = heap[pos];
                        heap[pos] = tmp;
                        pos = parent;
                    } else {
                        break;
                    }
                }
            }

            idx += 1;
        }

        // Remove lazily deleted heap entries from the top.
        let mut cleaning = true;
        while cleaning && heap.len() > 0 {
            let top = heap[0];
            let top_id = top % base;
            let top_id_u = top_id as usize;

            if active[top_id_u] {
                cleaning = false;
            } else {
                let hlen = heap.len();
                let last = heap[hlen - 1];
                heap.pop();

                let new_len = heap.len();
                if new_len > 0 {
                    heap[0] = last;

                    let mut pos: usize = 0;
                    let mut stop = false;

                    while !stop && pos < new_len {
                        let left = pos * 2 + 1;
                        let right = pos * 2 + 2;
                        let mut largest = pos;

                        if left < new_len {
                            if heap[left] > heap[largest] {
                                largest = left;
                            }
                        }

                        if right < new_len {
                            if heap[right] > heap[largest] {
                                largest = right;
                            }
                        }

                        if largest == pos {
                            stop = true;
                        } else {
                            let tmp = heap[pos];
                            heap[pos] = heap[largest];
                            heap[largest] = tmp;
                            pos = largest;
                        }
                    }
                }
            }
        }

        let mut cur_h: i64 = 0;
        if heap.len() > 0 {
            cur_h = heap[0] / base;
        }

        if cur_h != last_h {
            let mut point: Vec<i64> = Vec::new();
            point.push(x);
            point.push(cur_h);
            res.push(point);
            last_h = cur_h;
        }
    }

    res
}
