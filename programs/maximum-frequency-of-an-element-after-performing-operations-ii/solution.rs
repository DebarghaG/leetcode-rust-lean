pub fn max_frequency(nums: &[i64], k: i64, numOperations: i64) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }
    a.sort();

    let two_k = k + k;

    // Maximum number of elements that can fit into one interval of length 2*k.
    let mut max_window: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;
    while right < n {
        while left <= right && a[right] - a[left] > two_k {
            left += 1;
        }
        let len = (right - left + 1) as i64;
        if len > max_window {
            max_window = len;
        }
        right += 1;
    }

    let mut ans: i64 = 0;
    if max_window < numOperations {
        ans = max_window;
    } else {
        ans = numOperations;
    }

    // Check every possible target that already exists in the array.
    let mut g: usize = 0;
    let mut lo: usize = 0;
    let mut hi: usize = 0;

    while g < n {
        let y = a[g];
        let mut j = g + 1;
        while j < n && a[j] == y {
            j += 1;
        }
        let freq = (j - g) as i64;

        while lo < n && a[lo] < y - k {
            lo += 1;
        }

        if hi < lo {
            hi = lo;
        }
        while hi < n && a[hi] <= y + k {
            hi += 1;
        }

        let reachable = (hi - lo) as i64;
        let mut candidate = freq + numOperations;
        if reachable < candidate {
            candidate = reachable;
        }
        if candidate > ans {
            ans = candidate;
        }

        g = j;
    }

    ans
}
