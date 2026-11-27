pub fn unmarked_sum_array(nums: &[i64], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut marked: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < n {
        total += nums[i];
        marked.push(false);
        i += 1;
    }

    let mut order: Vec<usize> = Vec::new();
    let mut buf: Vec<usize> = Vec::new();
    i = 0;
    while i < n {
        order.push(i);
        buf.push(0);
        i += 1;
    }

    let mut width = 1;
    while width < n {
        let mut start = 0;
        while start < n {
            let mid_unclamped = start + width;
            let mut mid = mid_unclamped;
            if mid > n {
                mid = n;
            }

            let end_unclamped = start + width + width;
            let mut end = end_unclamped;
            if end > n {
                end = n;
            }

            if mid >= end {
                let mut t = start;
                while t < end {
                    buf[t] = order[t];
                    t += 1;
                }
            } else {
                let mut left = start;
                let mut right = mid;
                let mut out = start;

                while left < mid && right < end {
                    let li = order[left];
                    let rj = order[right];

                    let mut take_left = false;
                    if nums[li] < nums[rj] {
                        take_left = true;
                    } else if nums[li] > nums[rj] {
                        take_left = false;
                    } else {
                        if li < rj {
                            take_left = true;
                        } else {
                            take_left = false;
                        }
                    }

                    if take_left {
                        buf[out] = li;
                        left += 1;
                    } else {
                        buf[out] = rj;
                        right += 1;
                    }
                    out += 1;
                }

                while left < mid {
                    buf[out] = order[left];
                    left += 1;
                    out += 1;
                }

                while right < end {
                    buf[out] = order[right];
                    right += 1;
                    out += 1;
                }
            }

            start = end;
        }

        i = 0;
        while i < n {
            order[i] = buf[i];
            i += 1;
        }

        width = width * 2;
    }

    let mut answer: Vec<i64> = Vec::new();
    let mut pos: usize = 0;
    let mut q = 0;

    while q < queries.len() {
        let idx = queries[q][0] as usize;

        if !marked[idx] {
            marked[idx] = true;
            total -= nums[idx];
        }

        let mut need = queries[q][1];

        while need > 0 && pos < n {
            let id = order[pos];

            if marked[id] {
                pos += 1;
            } else {
                marked[id] = true;
                total -= nums[id];
                need -= 1;
                pos += 1;
            }
        }

        answer.push(total);
        q += 1;
    }

    answer
}
