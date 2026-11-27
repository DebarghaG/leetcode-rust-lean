pub fn smallest_distance_pair(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut sorted: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    // Iterative merge sort of sorted.
    if n > 1 {
        let mut temp: Vec<i64> = Vec::new();
        let mut t = 0;
        while t < n {
            temp.push(0);
            t += 1;
        }

        let mut width: usize = 1;
        while width < n {
            let double_width = width + width;
            let mut start: usize = 0;

            while start < n {
                let mid = if start + width < n {
                    start + width
                } else {
                    n
                };
                let end = if start + double_width < n {
                    start + double_width
                } else {
                    n
                };

                let mut left = start;
                let mut right = mid;
                let mut out = start;

                while left < mid && right < end {
                    if sorted[left] <= sorted[right] {
                        temp[out] = sorted[left];
                        left += 1;
                    } else {
                        temp[out] = sorted[right];
                        right += 1;
                    }
                    out += 1;
                }

                while left < mid {
                    temp[out] = sorted[left];
                    left += 1;
                    out += 1;
                }

                while right < end {
                    temp[out] = sorted[right];
                    right += 1;
                    out += 1;
                }

                start += double_width;
            }

            let mut j = 0;
            while j < n {
                sorted[j] = temp[j];
                j += 1;
            }

            width = double_width;
        }
    }

    let mut low: i64 = 0;
    let mut high: i64 = sorted[n - 1] - sorted[0];

    while low < high {
        let mid = low + (high - low) / 2;
        let count = count_pairs_within(&sorted, mid);

        if count >= k {
            high = mid;
        } else {
            low = mid + 1;
        }
    }

    low
}

fn count_pairs_within(sorted: &[i64], limit: i64) -> i64 {
    let n = sorted.len();
    let mut count: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;

    while right < n {
        while left < right && sorted[right] - sorted[left] > limit {
            left += 1;
        }

        count += (right - left) as i64;
        right += 1;
    }

    count
}
