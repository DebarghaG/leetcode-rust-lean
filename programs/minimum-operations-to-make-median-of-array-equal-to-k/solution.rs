pub fn min_operations_to_make_median_k(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    a.sort();

    let m = n / 2;
    let mut ans: i64 = 0;

    if a[m] > k {
        let mut j = 0;
        while j <= m {
            if a[j] > k {
                ans += a[j] - k;
            }
            j += 1;
        }
    } else if a[m] < k {
        let mut j = m;
        while j < n {
            if a[j] < k {
                ans += k - a[j];
            }
            j += 1;
        }
    }

    ans
}
