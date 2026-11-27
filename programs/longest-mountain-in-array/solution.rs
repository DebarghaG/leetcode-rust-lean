pub fn longest_mountain(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n < 3 {
        return 0;
    }

    let mut best: i64 = 0;
    let mut i: usize = 1;

    while i + 1 < n {
        if arr[i] > arr[i - 1] && arr[i] > arr[i + 1] {
            let mut left: usize = i;
            while left > 0 && arr[left - 1] < arr[left] {
                left -= 1;
            }

            let mut right: usize = i;
            while right + 1 < n && arr[right] > arr[right + 1] {
                right += 1;
            }

            let length = (right - left + 1) as i64;
            if length > best {
                best = length;
            }

            i = right;
        } else {
            i += 1;
        }
    }

    best
}
