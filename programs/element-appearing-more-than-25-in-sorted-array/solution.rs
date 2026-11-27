pub fn find_special_integer(arr: &[i64]) -> i64 {
    let n: usize = arr.len();
    let mut i: usize = 0;

    while i < n {
        let mut j: usize = i + 1;
        while j < n && arr[j] == arr[i] {
            j += 1;
        }

        let count: usize = j - i;
        if count * 4 > n {
            return arr[i];
        }

        i = j;
    }

    arr[0]
}
