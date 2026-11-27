pub fn find_length_of_shortest_subarray(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n <= 1 {
        return 0;
    }

    let mut i: usize = 0;
    while i + 1 < n && arr[i] <= arr[i + 1] {
        i += 1;
    }

    if i == n - 1 {
        return 0;
    }

    let mut j: usize = n - 1;
    while j > 0 && arr[j - 1] <= arr[j] {
        j -= 1;
    }

    let mut ans: usize = n - (i + 1);
    if j < ans {
        ans = j;
    }

    let mut q: usize = j;
    let mut p: usize = 0;

    while p <= i {
        while q < n && arr[q] < arr[p] {
            q += 1;
        }

        if q == n {
            break;
        }

        let removed = q - p - 1;
        if removed < ans {
            ans = removed;
        }

        p += 1;
    }

    ans as i64
}
