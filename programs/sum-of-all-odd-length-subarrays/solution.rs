pub fn sum_odd_length_subarrays(arr: &[i64]) -> i64 {
    let n: usize = arr.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i;
        let mut current_sum: i64 = 0;

        while j < n {
            current_sum += arr[j];
            let length: usize = j - i + 1;

            if length % 2 == 1 {
                total += current_sum;
            }

            j += 1;
        }

        i += 1;
    }

    total
}
