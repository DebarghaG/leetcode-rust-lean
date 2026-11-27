pub fn reverse_pairs(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 2 {
        return 0;
    }

    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        arr.push(nums[i]);
        i += 1;
    }

    let mut tmp: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut count: i64 = 0;
    let mut width: usize = 1;

    while width < n {
        let mut left: usize = 0;

        while left < n {
            let mut mid: usize = left + width;
            if mid > n {
                mid = n;
            }

            let mut right: usize = left + width + width;
            if right > n {
                right = n;
            }

            if mid < right {
                let mut j: usize = mid;
                let mut p: usize = left;

                while p < mid {
                    while j < right && arr[p] > 2 * arr[j] {
                        j += 1;
                    }
                    count += (j - mid) as i64;
                    p += 1;
                }

                let mut a: usize = left;
                let mut b: usize = mid;
                let mut k: usize = left;

                while a < mid && b < right {
                    if arr[a] <= arr[b] {
                        tmp[k] = arr[a];
                        a += 1;
                    } else {
                        tmp[k] = arr[b];
                        b += 1;
                    }
                    k += 1;
                }

                while a < mid {
                    tmp[k] = arr[a];
                    a += 1;
                    k += 1;
                }

                while b < right {
                    tmp[k] = arr[b];
                    b += 1;
                    k += 1;
                }

                let mut t: usize = left;
                while t < right {
                    arr[t] = tmp[t];
                    t += 1;
                }
            }

            left += width + width;
        }

        width += width;
    }

    count
}
