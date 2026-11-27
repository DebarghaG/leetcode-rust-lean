pub fn count_elements(arr: &[i64]) -> i64 {
    let n = arr.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let x = arr[i];
        let mut found: bool = false;
        let mut j: usize = 0;

        while j < n {
            if arr[j] == x + 1 {
                found = true;
            }
            j += 1;
        }

        if found {
            count += 1;
        }

        i += 1;
    }

    count
}
