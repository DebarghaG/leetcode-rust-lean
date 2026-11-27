pub fn minimum_difference(nums: &[i64], k: i64) -> i64 {
    if k <= 1 {
        return 0;
    }

    let n = nums.len();
    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }

    let mut a: usize = 1;
    while a < n {
        let key = sorted[a];
        let mut j: usize = a;
        while j > 0 && sorted[j - 1] > key {
            sorted[j] = sorted[j - 1];
            j -= 1;
        }
        sorted[j] = key;
        a += 1;
    }

    let w = k as usize;
    let mut ans = sorted[n - 1] - sorted[0];
    let mut left: usize = 0;

    while left + w <= n {
        let diff = sorted[left + w - 1] - sorted[left];
        if diff < ans {
            ans = diff;
        }
        left += 1;
    }

    ans
}
