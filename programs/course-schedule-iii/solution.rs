pub fn schedule_course(courses: &[Vec<i64>]) -> i64 {
    let n: usize = courses.len();
    if n == 0 {
        return 0;
    }

    let mut max_duration: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        let d: i64 = courses[i][0];
        if d > max_duration {
            max_duration = d;
        }
        i += 1;
    }

    let base: i64 = max_duration + 1;

    let mut keys: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let duration: i64 = courses[i][0];
        let last_day: i64 = courses[i][1];
        keys.push(last_day * base + duration);
        i += 1;
    }

    keys.sort();

    let mut total: i64 = 0;
    let mut heap: Vec<i64> = Vec::new();

    i = 0;
    while i < n {
        let key: i64 = keys[i];
        let duration: i64 = key % base;
        let last_day: i64 = key / base;

        if total + duration <= last_day {
            total = total + duration;
            heap.push(duration);

            let mut pos: usize = heap.len() - 1;
            while pos > 0 {
                let parent: usize = (pos - 1) / 2;
                if heap[parent] < heap[pos] {
                    let tmp: i64 = heap[parent];
                    heap[parent] = heap[pos];
                    heap[pos] = tmp;
                    pos = parent;
                } else {
                    break;
                }
            }
        } else {
            if heap.len() > 0 {
                let max_selected: i64 = heap[0];
                if max_selected > duration {
                    total = total - max_selected + duration;
                    heap[0] = duration;

                    let heap_len: usize = heap.len();
                    let mut pos: usize = 0;
                    while 2 * pos + 1 < heap_len {
                        let left: usize = 2 * pos + 1;
                        let right: usize = left + 1;
                        let mut largest: usize = pos;

                        if heap[left] > heap[largest] {
                            largest = left;
                        }
                        if right < heap_len && heap[right] > heap[largest] {
                            largest = right;
                        }

                        if largest == pos {
                            break;
                        }

                        let tmp: i64 = heap[pos];
                        heap[pos] = heap[largest];
                        heap[largest] = tmp;
                        pos = largest;
                    }
                }
            }
        }

        i += 1;
    }

    heap.len() as i64
}
