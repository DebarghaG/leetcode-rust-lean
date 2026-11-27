pub fn check_if_exist(arr: &[i64]) -> bool {
    let n = arr.len();
    let mut found: bool = false;
    let mut i: usize = 0;

    while i < n && !found {
        let mut j: usize = 0;

        while j < n && !found {
            if i != j && arr[i] == 2 * arr[j] {
                found = true;
            }
            j += 1;
        }

        i += 1;
    }

    found
}
