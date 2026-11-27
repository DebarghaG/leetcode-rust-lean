pub fn min_pair_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    // Build a max-heap.
    let mut start: usize = n / 2;
    while start > 0 {
        start -= 1;
        let mut root: usize = start;
        let mut go: bool = true;
        while go {
            let child = 2 * root + 1;
            if child >= n {
                go = false;
            } else {
                let mut swap_idx: usize = root;
                if v[swap_idx] < v[child] {
                    swap_idx = child;
                }
                let right = child + 1;
                if right < n && v[swap_idx] < v[right] {
                    swap_idx = right;
                }
                if swap_idx == root {
                    go = false;
                } else {
                    let tmp = v[root];
                    v[root] = v[swap_idx];
                    v[swap_idx] = tmp;
                    root = swap_idx;
                }
            }
        }
    }

    // Extract elements from the heap to get an ascending sorted vector.
    let mut end: usize = n;
    while end > 1 {
        let tmp = v[0];
        v[0] = v[end - 1];
        v[end - 1] = tmp;
        end -= 1;

        let mut root: usize = 0;
        let mut go: bool = true;
        while go {
            let child = 2 * root + 1;
            if child >= end {
                go = false;
            } else {
                let mut swap_idx: usize = root;
                if v[swap_idx] < v[child] {
                    swap_idx = child;
                }
                let right = child + 1;
                if right < end && v[swap_idx] < v[right] {
                    swap_idx = right;
                }
                if swap_idx == root {
                    go = false;
                } else {
                    let tmp2 = v[root];
                    v[root] = v[swap_idx];
                    v[swap_idx] = tmp2;
                    root = swap_idx;
                }
            }
        }
    }

    // Pair the smallest with the largest, the second smallest with the
    // second largest, and so on. The answer is the maximum of these sums.
    let mut ans: i64 = 0;
    let half = n / 2;
    let mut left: usize = 0;
    while left < half {
        let pair_sum = v[left] + v[n - 1 - left];
        if pair_sum > ans {
            ans = pair_sum;
        }
        left += 1;
    }

    ans
}
