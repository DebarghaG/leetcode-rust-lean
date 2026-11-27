pub fn max_num_of_marked_indices(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }
    a.sort();

    let mut low: usize = 0;
    let mut high: usize = n / 2 + 1;

    while low + 1 < high {
        let mid: usize = (low + high) / 2;
        let mut ok: bool = true;
        let mut j: usize = 0;

        while j < mid {
            if 2 * a[j] > a[n - mid + j] {
                ok = false;
                j = mid;
            } else {
                j += 1;
            }
        }

        if ok {
            low = mid;
        } else {
            high = mid;
        }
    }

    let mut ans: i64 = 0;
    let mut k: usize = 0;
    while k < low {
        ans += 2;
        k += 1;
    }

    ans
}
