pub fn num_of_subarrays(arr: &[i64], k: i64, threshold: i64) -> i64 {
    let n: usize = arr.len();

    if k <= 0 {
        return 0;
    }

    let k_usize: usize = k as usize;

    if k_usize > n {
        return 0;
    }

    let target: i64 = k * threshold;

    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < k_usize {
        sum += arr[i];
        i += 1;
    }

    let mut count: i64 = 0;
    if sum >= target {
        count += 1;
    }

    let mut start: usize = 1;
    while start + k_usize <= n {
        sum = sum - arr[start - 1] + arr[start + k_usize - 1];
        if sum >= target {
            count += 1;
        }
        start += 1;
    }

    count
}
