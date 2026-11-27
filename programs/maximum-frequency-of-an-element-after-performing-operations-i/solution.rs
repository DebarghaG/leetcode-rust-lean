pub fn max_frequency(nums: &[i64], k: i64, numOperations: i64) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        a.push(nums[idx]);
        idx += 1;
    }
    a.sort();

    // Maximum number of elements that can be brought to some common value
    // without paying attention to already-existing equal elements.
    let mut left: usize = 0;
    let mut right: usize = 0;
    let mut window_count: i64 = 0;
    let mut max_window: i64 = 0;

    while right < n {
        window_count += 1;
        while a[right] - a[left] > 2 * k {
            window_count -= 1;
            left += 1;
        }
        if window_count > max_window {
            max_window = window_count;
        }
        right += 1;
    }

    let mut ans: i64 = if numOperations < max_window {
        numOperations
    } else {
        max_window
    };

    let mut i: usize = 0;
    let mut l: usize = 0;
    let mut r: usize = 0;
    let mut c_count: i64 = 0;

    while i < n {
        let v = a[i];

        let mut freq: i64 = 0;
        let mut j: usize = i;
        while j < n && a[j] == v {
            freq += 1;
            j += 1;
        }

        while r < n && a[r] <= v + k {
            c_count += 1;
            r += 1;
        }

        while l < n && a[l] < v - k {
            c_count -= 1;
            l += 1;
        }

        let possible: i64 = freq + numOperations;
        let candidate: i64 = if c_count < possible {
            c_count
        } else {
            possible
        };

        if candidate > ans {
            ans = candidate;
        }

        i = j;
    }

    ans
}
