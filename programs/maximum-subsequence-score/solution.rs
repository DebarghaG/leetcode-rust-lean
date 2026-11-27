pub fn max_score(nums1: &[i64], nums2: &[i64], k: i64) -> i64 {
    let n = nums1.len();
    if n == 0 {
        return 0;
    }

    let mut max_v = nums2[0];
    let mut i = 1usize;
    while i < n {
        if nums2[i] > max_v {
            max_v = nums2[i];
        }
        i += 1;
    }

    let size = (max_v as usize) + 1;

    let mut counts: Vec<i64> = Vec::new();
    let mut z = 0usize;
    while z < size {
        counts.push(0);
        z += 1;
    }

    i = 0usize;
    while i < n {
        let v = nums2[i] as usize;
        counts[v] += 1;
        i += 1;
    }

    let mut start: Vec<i64> = Vec::new();
    z = 0usize;
    while z < size {
        start.push(0);
        z += 1;
    }

    let mut pos: i64 = 0;
    let mut val = max_v;
    while val >= 0 {
        let vu = val as usize;
        start[vu] = pos;
        pos += counts[vu];
        val -= 1;
    }

    let mut next: Vec<i64> = Vec::new();
    z = 0usize;
    while z < size {
        next.push(start[z]);
        z += 1;
    }

    let mut order: Vec<i64> = Vec::new();
    z = 0usize;
    while z < n {
        order.push(0);
        z += 1;
    }

    i = 0usize;
    while i < n {
        let v = nums2[i] as usize;
        let p = next[v] as usize;
        order[p] = i as i64;
        next[v] = next[v] + 1;
        i += 1;
    }

    let mut heap: Vec<i64> = Vec::new();
    z = 0usize;
    while z < n {
        heap.push(0);
        z += 1;
    }

    let mut hlen: usize = 0;
    let k_u = k as usize;
    let mut sum: i64 = 0;
    let mut ans: i64 = 0;

    let mut oi = 0usize;
    while oi < n {
        let id = order[oi] as usize;
        let x = nums1[id];

        heap[hlen] = x;
        let mut j = hlen;
        hlen += 1;

        while j > 0 {
            let p = (j - 1) / 2;
            if heap[p] <= heap[j] {
                break;
            }
            let tmp = heap[p];
            heap[p] = heap[j];
            heap[j] = tmp;
            j = p;
        }

        sum += x;

        if hlen > k_u {
            let removed = heap[0];
            sum -= removed;

            let last = heap[hlen - 1];
            hlen -= 1;

            if hlen > 0 {
                heap[0] = last;
                let mut t = 0usize;
                let mut done = false;

                while !done {
                    let left = t * 2 + 1;
                    let right = left + 1;
                    let mut smallest = t;

                    if left < hlen && heap[left] < heap[smallest] {
                        smallest = left;
                    }
                    if right < hlen && heap[right] < heap[smallest] {
                        smallest = right;
                    }

                    if smallest == t {
                        done = true;
                    } else {
                        let tmp = heap[t];
                        heap[t] = heap[smallest];
                        heap[smallest] = tmp;
                        t = smallest;
                    }
                }
            }
        }

        if hlen == k_u {
            let cand = sum * nums2[id];
            if cand > ans {
                ans = cand;
            }
        }

        oi += 1;
    }

    ans
}
