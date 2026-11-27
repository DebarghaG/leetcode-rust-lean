pub fn minimum_deviation(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut heap: Vec<i64> = Vec::new();
    let mut min_v: i64 = 1000000000000000000;
    let mut i: usize = 0;

    while i < n {
        let mut val = nums[i];
        if val % 2 != 0 {
            val = val * 2;
        }

        if val < min_v {
            min_v = val;
        }

        let mut idx = heap.len();
        heap.push(val);
        let mut done = false;
        while !done && idx > 0 {
            let p = (idx - 1) / 2;
            if heap[p] < heap[idx] {
                let tmp = heap[p];
                heap[p] = heap[idx];
                heap[idx] = tmp;
                idx = p;
            } else {
                done = true;
            }
        }

        i = i + 1;
    }

    let mut ans = heap[0] - min_v;
    let mut stop = false;

    while !stop {
        let maxv = heap[0];
        if maxv % 2 != 0 {
            stop = true;
        } else {
            let nv = maxv / 2;
            heap[0] = nv;
            if nv < min_v {
                min_v = nv;
            }

            let len = heap.len();
            let mut idx = 0;
            let mut sift_done = false;
            while !sift_done {
                let l = 2 * idx + 1;
                let r = l + 1;
                let mut largest = idx;

                if l < len && heap[l] > heap[largest] {
                    largest = l;
                }
                if r < len && heap[r] > heap[largest] {
                    largest = r;
                }

                if largest == idx {
                    sift_done = true;
                } else {
                    let tmp = heap[idx];
                    heap[idx] = heap[largest];
                    heap[largest] = tmp;
                    idx = largest;
                }
            }

            let cur_max = heap[0];
            let dev = cur_max - min_v;
            if dev < ans {
                ans = dev;
            }
        }
    }

    ans
}
