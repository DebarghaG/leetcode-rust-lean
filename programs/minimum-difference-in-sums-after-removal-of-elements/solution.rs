fn heap_push_max(h: &mut Vec<i64>, x: i64) {
    h.push(x);
    let mut i = h.len() - 1;
    let mut running = true;
    while running && i > 0 {
        let p = (i - 1) / 2;
        if h[i] > h[p] {
            let tmp = h[i];
            h[i] = h[p];
            h[p] = tmp;
            i = p;
        } else {
            running = false;
        }
    }
}

fn heap_pop_max(h: &mut Vec<i64>) -> i64 {
    let len = h.len();
    let top = h[0];
    let last = h[len - 1];
    h.pop();
    let new_len = h.len();

    if new_len > 0 {
        h[0] = last;
        let mut i = 0;
        let mut running = true;
        while running {
            let left = 2 * i + 1;
            if left >= new_len {
                running = false;
            } else {
                let mut largest = i;
                if h[left] > h[largest] {
                    largest = left;
                }
                let right = left + 1;
                if right < new_len && h[right] > h[largest] {
                    largest = right;
                }
                if largest == i {
                    running = false;
                } else {
                    let tmp = h[i];
                    h[i] = h[largest];
                    h[largest] = tmp;
                    i = largest;
                }
            }
        }
    }

    top
}

fn heap_push_min(h: &mut Vec<i64>, x: i64) {
    h.push(x);
    let mut i = h.len() - 1;
    let mut running = true;
    while running && i > 0 {
        let p = (i - 1) / 2;
        if h[i] < h[p] {
            let tmp = h[i];
            h[i] = h[p];
            h[p] = tmp;
            i = p;
        } else {
            running = false;
        }
    }
}

fn heap_pop_min(h: &mut Vec<i64>) -> i64 {
    let len = h.len();
    let top = h[0];
    let last = h[len - 1];
    h.pop();
    let new_len = h.len();

    if new_len > 0 {
        h[0] = last;
        let mut i = 0;
        let mut running = true;
        while running {
            let left = 2 * i + 1;
            if left >= new_len {
                running = false;
            } else {
                let mut smallest = i;
                if h[left] < h[smallest] {
                    smallest = left;
                }
                let right = left + 1;
                if right < new_len && h[right] < h[smallest] {
                    smallest = right;
                }
                if smallest == i {
                    running = false;
                } else {
                    let tmp = h[i];
                    h[i] = h[smallest];
                    h[smallest] = tmp;
                    i = smallest;
                }
            }
        }
    }

    top
}

pub fn minimum_difference(nums: &[i64]) -> i64 {
    let m = nums.len();
    let n = m / 3;

    if n == 0 {
        return 0;
    }

    let mut left: Vec<i64> = Vec::new();
    let mut k = 0;
    while k <= m {
        left.push(0);
        k += 1;
    }

    let mut max_heap: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut i = 0;

    while i < m {
        let x = nums[i];

        if max_heap.len() < n {
            heap_push_max(&mut max_heap, x);
            sum += x;
        } else if x < max_heap[0] {
            let old = heap_pop_max(&mut max_heap);
            sum -= old;
            heap_push_max(&mut max_heap, x);
            sum += x;
        }

        if max_heap.len() == n {
            left[i + 1] = sum;
        }

        i += 1;
    }

    let mut min_heap: Vec<i64> = Vec::new();
    sum = 0;
    let mut ans: i64 = 1000000000000000000;
    let mut pos = m;

    while pos > 0 {
        pos -= 1;
        let x = nums[pos];

        if min_heap.len() < n {
            heap_push_min(&mut min_heap, x);
            sum += x;
        } else if x > min_heap[0] {
            let old = heap_pop_min(&mut min_heap);
            sum -= old;
            heap_push_min(&mut min_heap, x);
            sum += x;
        }

        if min_heap.len() == n && pos >= n && pos <= 2 * n {
            let diff = left[pos] - sum;
            if diff < ans {
                ans = diff;
            }
        }
    }

    ans
}
