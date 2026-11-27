pub fn minimum_deletions(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut min_idx: usize = 0;
    let mut max_idx: usize = 0;

    let mut i: usize = 1;
    while i < n {
        if nums[i] < nums[min_idx] {
            min_idx = i;
        }
        if nums[i] > nums[max_idx] {
            max_idx = i;
        }
        i += 1;
    }

    let mut l = min_idx;
    let mut r = max_idx;
    if l > r {
        let temp = l;
        l = r;
        r = temp;
    }

    let remove_from_front = r + 1;
    let remove_from_back = n - l;
    let remove_both_ends = l + 1 + (n - r);

    let mut ans = remove_from_front;
    if remove_from_back < ans {
        ans = remove_from_back;
    }
    if remove_both_ends < ans {
        ans = remove_both_ends;
    }

    ans as i64
}
