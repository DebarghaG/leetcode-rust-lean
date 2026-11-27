pub fn triangle_number(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n < 3 {
        return 0;
    }

    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        arr.push(nums[i]);
        i += 1;
    }

    let mut i: usize = 1;
    while i < n {
        let key: i64 = arr[i];
        let mut j: usize = i;
        while j > 0 {
            if arr[j - 1] > key {
                arr[j] = arr[j - 1];
                j -= 1;
            } else {
                break;
            }
        }
        arr[j] = key;
        i += 1;
    }

    let mut count: i64 = 0;
    let mut k: usize = 2;
    while k < n {
        let mut left: usize = 0;
        let mut right: usize = k - 1;

        while left < right {
            if arr[left] + arr[right] > arr[k] {
                let add: i64 = (right - left) as i64;
                count += add;
                right -= 1;
            } else {
                left += 1;
            }
        }

        k += 1;
    }

    count
}
