pub fn make_pref_sum_non_negative(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut heap: Vec<i64> = Vec::new();
    let mut sum: i64 = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];
        sum += x;

        if x < 0 {
            let mut idx = heap.len();
            heap.push(x);
            let mut up = true;

            while up && idx > 0 {
                let parent = (idx - 1) / 2;
                if heap[idx] < heap[parent] {
                    let tmp = heap[idx];
                    heap[idx] = heap[parent];
                    heap[parent] = tmp;
                    idx = parent;
                } else {
                    up = false;
                }
            }
        }

        if sum < 0 {
            let hlen = heap.len();
            let removed = heap[0];
            let last = heap[hlen - 1];
            let _ = heap.pop();

            if hlen > 1 {
                heap[0] = last;
                let mut idx = 0;
                let mut going = true;

                while going {
                    let cur_len = heap.len();
                    let left = 2 * idx + 1;
                    let right = 2 * idx + 2;
                    let mut smallest = idx;

                    if left < cur_len && heap[left] < heap[smallest] {
                        smallest = left;
                    }
                    if right < cur_len && heap[right] < heap[smallest] {
                        smallest = right;
                    }

                    if smallest == idx {
                        going = false;
                    } else {
                        let tmp = heap[idx];
                        heap[idx] = heap[smallest];
                        heap[smallest] = tmp;
                        idx = smallest;
                    }
                }
            }

            sum -= removed;
            ans += 1;
        }

        i += 1;
    }

    ans
}
