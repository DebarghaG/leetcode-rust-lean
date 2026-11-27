pub fn three_sum_smaller(nums: &[i64], target: i64) -> i64 {
    let n: usize = nums.len();

    let mut a: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < n {
        a.push(nums[p]);
        p += 1;
    }

    // Insertion sort in ascending order.
    let mut i: usize = 1;
    while i < n {
        let key: i64 = a[i];
        let mut j: usize = i;
        while j > 0 && a[j - 1] > key {
            a[j] = a[j - 1];
            j -= 1;
        }
        a[j] = key;
        i += 1;
    }

    let mut count: i64 = 0;
    let mut first: usize = 0;

    while first + 2 < n {
        let mut left: usize = first + 1;
        let mut right: usize = n - 1;

        while left < right {
            let sum: i64 = a[first] + a[left] + a[right];
            if sum < target {
                count += (right - left) as i64;
                left += 1;
            } else {
                right -= 1;
            }
        }

        first += 1;
    }

    count
}
