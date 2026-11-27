fn max_heap_push(h: &mut Vec<i64>, val: i64) {
    let mut pos = h.len();
    h.push(val);
    while pos > 0 {
        let parent = (pos - 1) / 2;
        if h[parent] >= val {
            break;
        }
        h[pos] = h[parent];
        pos = parent;
    }
    h[pos] = val;
}

fn max_heap_pop(h: &mut Vec<i64>) {
    let last = h[h.len() - 1];
    h.pop();
    let n = h.len();
    if n > 0 {
        let mut pos = 0;
        while pos < n {
            let left = 2 * pos + 1;
            if left >= n {
                break;
            }
            let mut child = left;
            let right = left + 1;
            if right < n && h[right] > h[left] {
                child = right;
            }
            if h[child] <= last {
                break;
            }
            h[pos] = h[child];
            pos = child;
        }
        h[pos] = last;
    }
}

fn min_heap_push(
    hs: &mut Vec<i64>,
    hi: &mut Vec<usize>,
    val: i64,
    idx: usize,
) {
    let mut pos = hs.len();
    hs.push(val);
    hi.push(idx);
    while pos > 0 {
        let parent = (pos - 1) / 2;
        if hs[parent] <= val {
            break;
        }
        hs[pos] = hs[parent];
        hi[pos] = hi[parent];
        pos = parent;
    }
    hs[pos] = val;
    hi[pos] = idx;
}

fn min_heap_pop(hs: &mut Vec<i64>, hi: &mut Vec<usize>) {
    let last_sum = hs[hs.len() - 1];
    let last_idx = hi[hi.len() - 1];
    hs.pop();
    hi.pop();

    let n = hs.len();
    if n > 0 {
        let mut pos = 0;
        while pos < n {
            let left = 2 * pos + 1;
            if left >= n {
                break;
            }
            let mut child = left;
            let right = left + 1;
            if right < n && hs[right] < hs[left] {
                child = right;
            }
            if hs[child] >= last_sum {
                break;
            }
            hs[pos] = hs[child];
            hi[pos] = hi[child];
            pos = child;
        }
        hs[pos] = last_sum;
        hi[pos] = last_idx;
    }
}

pub fn k_sum(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let kk = k as usize;

    let mut total: i64 = 0;
    let mut zeros: usize = 0;

    let mut i = 0;
    while i < n {
        let x = nums[i];
        if x > 0 {
            total += x;
        }
        if x == 0 {
            zeros += 1;
        }
        i += 1;
    }

    if kk <= 1 {
        return total;
    }

    let mut zadd = zeros;
    if zadd > kk {
        zadd = kk;
    }

    let mut need_nonzero: usize = 0;
    if kk > zeros {
        need_nonzero = kk - zeros;
    }

    let mut keep: Vec<i64> = Vec::new();
    if need_nonzero > 0 {
        i = 0;
        while i < n {
            let x = nums[i];
            if x != 0 {
                let mut c = x;
                if c < 0 {
                    c = -c;
                }

                if keep.len() < need_nonzero {
                    max_heap_push(&mut keep, c);
                } else if c < keep[0] {
                    max_heap_pop(&mut keep);
                    max_heap_push(&mut keep, c);
                }
            }
            i += 1;
        }
    }

    let mut costs: Vec<i64> = Vec::new();

    let mut z = 0;
    while z < zadd {
        costs.push(0);
        z += 1;
    }

    let mut j = 0;
    while j < keep.len() {
        costs.push(keep[j]);
        j += 1;
    }

    let m0 = costs.len();
    let mut a = 1;
    while a < m0 {
        let val = costs[a];
        let mut b = a;
        while b > 0 {
            if costs[b - 1] <= val {
                break;
            }
            costs[b] = costs[b - 1];
            b -= 1;
        }
        costs[b] = val;
        a += 1;
    }

    let m = costs.len();
    if m == 0 {
        return total;
    }

    let mut hs: Vec<i64> = Vec::new();
    let mut hi: Vec<usize> = Vec::new();
    min_heap_push(&mut hs, &mut hi, costs[0], 0);

    let limit = kk - 2;
    let mut pop_count: usize = 0;

    while pop_count < limit {
        let s = hs[0];
        let idx = hi[0];
        min_heap_pop(&mut hs, &mut hi);

        let next = idx + 1;
        if next < m {
            min_heap_push(&mut hs, &mut hi, s + costs[next], next);
            min_heap_push(
                &mut hs,
                &mut hi,
                s - costs[idx] + costs[next],
                next,
            );
        }

        pop_count += 1;
    }

    total - hs[0]
}
