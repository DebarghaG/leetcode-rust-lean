pub fn smallest_range_ii(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let mut start = n / 2;
    while start > 0 {
        start -= 1;
        let mut root = start;
        let mut active = true;
        while active {
            let left = root * 2 + 1;
            if left >= n {
                active = false;
            } else {
                let mut largest = root;
                if a[largest] < a[left] {
                    largest = left;
                }
                let right = left + 1;
                if right < n {
                    if a[largest] < a[right] {
                        largest = right;
                    }
                }
                if largest == root {
                    active = false;
                } else {
                    let tmp = a[root];
                    a[root] = a[largest];
                    a[largest] = tmp;
                    root = largest;
                }
            }
        }
    }

    let mut end = n;
    while end > 1 {
        end -= 1;

        let tmp = a[0];
        a[0] = a[end];
        a[end] = tmp;

        let mut root = 0;
        let mut active = true;
        while active {
            let left = root * 2 + 1;
            if left >= end {
                active = false;
            } else {
                let mut largest = root;
                if a[largest] < a[left] {
                    largest = left;
                }
                let right = left + 1;
                if right < end {
                    if a[largest] < a[right] {
                        largest = right;
                    }
                }
                if largest == root {
                    active = false;
                } else {
                    let tmp2 = a[root];
                    a[root] = a[largest];
                    a[largest] = tmp2;
                    root = largest;
                }
            }
        }
    }

    let mut ans = a[n - 1] - a[0];
    let mut idx = 0;

    while idx + 1 < n {
        let lo1 = a[0] + k;
        let lo2 = a[idx + 1] - k;
        let mut lo = lo1;
        if lo2 < lo {
            lo = lo2;
        }

        let hi1 = a[idx] + k;
        let hi2 = a[n - 1] - k;
        let mut hi = hi1;
        if hi2 > hi {
            hi = hi2;
        }

        let score = hi - lo;
        if score < ans {
            ans = score;
        }

        idx += 1;
    }

    ans
}
