fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        temp.push(0);
        i += 1;
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

            let mut p = left;
            let mut q = mid;
            let mut t = left;

            while p < mid && q < right {
                if v[p] <= v[q] {
                    temp[t] = v[p];
                    p += 1;
                } else {
                    temp[t] = v[q];
                    q += 1;
                }
                t += 1;
            }

            while p < mid {
                temp[t] = v[p];
                p += 1;
                t += 1;
            }

            while q < right {
                temp[t] = v[q];
                q += 1;
                t += 1;
            }

            left = left + width + width;
        }

        let mut j: usize = 0;
        while j < n {
            v[j] = temp[j];
            j += 1;
        }

        width = width + width;
    }
}

pub fn find_maximized_capital(k: i64, w: i64, profits: &[i64], capital: &[i64]) -> i64 {
    let n = profits.len();
    if n == 0 || k <= 0 {
        return w;
    }

    let mut mult: i64 = 1;
    let mut i: usize = 0;
    while i < n {
        let p = profits[i];
        if p + 1 > mult {
            mult = p + 1;
        }
        i += 1;
    }

    let mut keys: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        keys.push(capital[i] * mult + profits[i]);
        i += 1;
    }
    sort_i64(&mut keys);

    let mut heap: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        heap.push(0);
        i += 1;
    }
    let mut heap_len: usize = 0;

    let mut cur: i64 = w;
    let mut next: usize = 0;
    let mut done: i64 = 0;

    while done < k {
        while next < n {
            let key = keys[next];
            let cap = key / mult;
            if cap <= cur {
                let profit = key % mult;

                heap[heap_len] = profit;
                let mut pos: usize = heap_len;
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
                heap_len += 1;
                next += 1;
            } else {
                break;
            }
        }

        if heap_len == 0 {
            break;
        }

        let best = heap[0];
        heap_len -= 1;
        let last = heap[heap_len];

        if heap_len > 0 {
            heap[0] = last;
            let mut pos: usize = 0;
            let mut going: bool = true;

            while going {
                let left = 2 * pos + 1;
                let right = 2 * pos + 2;
                let mut largest = pos;

                if left < heap_len {
                    if heap[left] > heap[largest] {
                        largest = left;
                    }
                }

                if right < heap_len {
                    if heap[right] > heap[largest] {
                        largest = right;
                    }
                }

                if largest != pos {
                    let tmp = heap[pos];
                    heap[pos] = heap[largest];
                    heap[largest] = tmp;
                    pos = largest;
                } else {
                    going = false;
                }
            }
        }

        cur += best;
        done += 1;
    }

    cur
}
