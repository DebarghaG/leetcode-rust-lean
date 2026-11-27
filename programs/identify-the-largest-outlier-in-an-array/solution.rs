fn sort_copy(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        arr.push(nums[i]);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut start: usize = 0;
        while start < n {
            let mut mid: usize = start + width;
            if mid > n {
                mid = n;
            }
            let mut end: usize = start + width + width;
            if end > n {
                end = n;
            }

            let mut l: usize = start;
            let mut r: usize = mid;
            while l < mid && r < end {
                if arr[l] <= arr[r] {
                    merged.push(arr[l]);
                    l += 1;
                } else {
                    merged.push(arr[r]);
                    r += 1;
                }
            }
            while l < mid {
                merged.push(arr[l]);
                l += 1;
            }
            while r < end {
                merged.push(arr[r]);
                r += 1;
            }

            start = end;
        }

        arr = merged;
        width = width + width;
    }

    arr
}

fn lower_bound(a: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = a.len();
    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if a[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn upper_bound(a: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = a.len();
    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if a[mid] <= x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn count_value(a: &[i64], x: i64) -> usize {
    let lo = lower_bound(a, x);
    let hi = upper_bound(a, x);
    hi - lo
}

pub fn get_largest_outlier(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        total = total + nums[i];
        i += 1;
    }

    let sorted = sort_copy(nums);

    let mut ans: i64 = 0;
    let mut found: bool = false;

    i = 0;
    while i < n {
        let outlier = nums[i];
        let diff = total - outlier;
        let sum_value = diff / 2;

        if sum_value * 2 == diff {
            let cnt = count_value(&sorted, sum_value);

            let mut need: usize = 1;
            if sum_value == outlier {
                need = 2;
            }

            if cnt >= need {
                if found == false {
                    ans = outlier;
                    found = true;
                } else {
                    if outlier > ans {
                        ans = outlier;
                    }
                }
            }
        }

        i += 1;
    }

    ans
}
