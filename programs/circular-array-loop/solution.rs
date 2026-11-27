pub fn circular_array_loop(nums: &[i64]) -> bool {
    let n: usize = nums.len();
    let n_i: i64 = n as i64;

    let mut result: bool = false;
    let mut start: usize = 0;

    while start < n && !result {
        let forward: bool = nums[start] > 0;
        let mut cur: usize = start;
        let mut length: i64 = 0;
        let mut same_direction: bool = true;

        while same_direction && length < n_i {
            let step: i64 = nums[cur];

            if (step > 0) != forward {
                same_direction = false;
            } else {
                let mut next_i: i64 = cur as i64 + step;

                if next_i >= n_i {
                    next_i = next_i % n_i;
                } else {
                    if next_i < 0 {
                        next_i = next_i % n_i;
                        if next_i < 0 {
                            next_i = next_i + n_i;
                        }
                    }
                }

                let next: usize = next_i as usize;

                if next == cur {
                    same_direction = false;
                } else {
                    length = length + 1;
                    cur = next;

                    if cur == start {
                        if length > 1 {
                            result = true;
                        }
                        same_direction = false;
                    }
                }
            }
        }

        start = start + 1;
    }

    result
}
