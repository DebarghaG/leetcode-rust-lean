pub fn max_chunks_to_sorted(arr: &[i64]) -> i64 {
    let n = arr.len();
    let mut chunks: i64 = 0;
    let mut max_so_far: i64 = -1;
    let mut i: usize = 0;

    while i < n {
        if arr[i] > max_so_far {
            max_so_far = arr[i];
        }
        if max_so_far == i as i64 {
            chunks += 1;
        }
        i += 1;
    }

    chunks
}
