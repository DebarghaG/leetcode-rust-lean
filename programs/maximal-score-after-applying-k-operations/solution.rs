pub fn max_kelements(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut heap: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        heap.push(nums[i]);
        i += 1;
    }

    // Build a max-heap.
    let mut start = n / 2;
    while start > 0 {
        start -= 1;

        let mut pos = start;
        while pos < n {
            let left = pos * 2 + 1;
            let right = left + 1;
            let mut largest = pos;

            if left < n && heap[left] > heap[largest] {
                largest = left;
            }
            if right < n && heap[right] > heap[largest] {
                largest = right;
            }

            if largest == pos {
                pos = n;
            } else {
                let tmp = heap[pos];
                heap[pos] = heap[largest];
                heap[largest] = tmp;
                pos = largest;
            }
        }
    }

    let mut score: i64 = 0;
    let mut ops: i64 = 0;

    while ops < k {
        let top = heap[0];
        score += top;

        heap[0] = (top + 2) / 3;

        // Restore the max-heap property after changing the root.
        let mut pos = 0usize;
        while pos < n {
            let left = pos * 2 + 1;
            let right = left + 1;
            let mut largest = pos;

            if left < n && heap[left] > heap[largest] {
                largest = left;
            }
            if right < n && heap[right] > heap[largest] {
                largest = right;
            }

            if largest == pos {
                pos = n;
            } else {
                let tmp = heap[pos];
                heap[pos] = heap[largest];
                heap[largest] = tmp;
                pos = largest;
            }
        }

        ops += 1;
    }

    score
}
