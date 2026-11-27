pub fn find_max_sum(nums1: &[i64], nums2: &[i64], k: i64) -> Vec<i64> {
    let n: usize = nums1.len();

    let mut ans: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        ans.push(0);
        z += 1;
    }

    if n == 0 {
        return ans;
    }

    let mut order: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        order.push(i as i64);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let m1 = start + width;
            let mid = if m1 < n { m1 } else { n };

            let e1 = start + 2 * width;
            let end = if e1 < n { e1 } else { n };

            let mut a: usize = start;
            let mut b: usize = mid;

            while a < mid && b < end {
                let ia = order[a] as usize;
                let ib = order[b] as usize;

                if nums1[ia] <= nums1[ib] {
                    merged.push(order[a]);
                    a += 1;
                } else {
                    merged.push(order[b]);
                    b += 1;
                }
            }

            while a < mid {
                merged.push(order[a]);
                a += 1;
            }

            while b < end {
                merged.push(order[b]);
                b += 1;
            }

            start = end;
        }

        order = merged;
        width = width * 2;
    }

    let k_usize: usize = if k > 0 { k as usize } else { 0 };

    let mut heap: Vec<i64> = Vec::new();
    let mut cur_sum: i64 = 0;
    let mut p: usize = 0;

    while p < n {
        let group_val = nums1[order[p] as usize];

        let mut q: usize = p + 1;
        while q < n && nums1[order[q] as usize] == group_val {
            q += 1;
        }

        let mut t: usize = p;
        while t < q {
            let idx = order[t] as usize;
            ans[idx] = cur_sum;
            t += 1;
        }

        t = p;
        while t < q {
            let idx = order[t] as usize;
            let x = nums2[idx];

            if k_usize > 0 {
                if heap.len() < k_usize {
                    heap.push(x);

                    let mut pos = heap.len() - 1;
                    while pos > 0 {
                        let parent = (pos - 1) / 2;

                        if heap[pos] < heap[parent] {
                            let tmp = heap[pos];
                            heap[pos] = heap[parent];
                            heap[parent] = tmp;
                            pos = parent;
                        } else {
                            break;
                        }
                    }

                    cur_sum += x;
                } else if x > heap[0] {
                    let old = heap[0];
                    heap[0] = x;

                    let len = heap.len();
                    let mut pos: usize = 0;

                    while pos < len {
                        let left = 2 * pos + 1;
                        if left >= len {
                            break;
                        }

                        let right = left + 1;
                        let mut smallest = left;

                        if right < len && heap[right] < heap[left] {
                            smallest = right;
                        }

                        if heap[smallest] < heap[pos] {
                            let tmp = heap[pos];
                            heap[pos] = heap[smallest];
                            heap[smallest] = tmp;
                            pos = smallest;
                        } else {
                            break;
                        }
                    }

                    cur_sum += x - old;
                }
            }

            t += 1;
        }

        p = q;
    }

    ans
}
