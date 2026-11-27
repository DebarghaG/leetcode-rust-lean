pub fn three_sum_closest(nums: &[i64], target: i64) -> i64 {
    let n = nums.len();

    let mut arr: Vec<i64> = Vec::new();
    let mut k = 0;
    while k < n {
        arr.push(nums[k]);
        k += 1;
    }

    // Selection sort the copied array.
    let mut i = 0;
    while i < n {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        if min_idx != i {
            let tmp = arr[i];
            arr[i] = arr[min_idx];
            arr[min_idx] = tmp;
        }
        i += 1;
    }

    let mut best = arr[0] + arr[1] + arr[2];
    let mut found_exact = false;

    let mut i = 0;
    while i + 2 < n && !found_exact {
        let mut left = i + 1;
        let mut right = n - 1;

        while left < right && !found_exact {
            let sum = arr[i] + arr[left] + arr[right];

            let diff = if sum > target {
                sum - target
            } else {
                target - sum
            };

            let best_diff = if best > target {
                best - target
            } else {
                target - best
            };

            if diff < best_diff {
                best = sum;
            }

            if sum < target {
                left += 1;
            } else if sum > target {
                right -= 1;
            } else {
                best = sum;
                found_exact = true;
            }
        }

        i += 1;
    }

    best
}
