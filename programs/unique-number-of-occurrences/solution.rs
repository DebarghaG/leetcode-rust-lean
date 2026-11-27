pub fn unique_occurrences(arr: &[i64]) -> bool {
    let n = arr.len();
    let mut counts: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let value = arr[i];

        let mut appeared_before: bool = false;
        let mut k: usize = 0;
        while k < i {
            if arr[k] == value {
                appeared_before = true;
                break;
            }
            k += 1;
        }

        if !appeared_before {
            let mut count: i64 = 0;
            let mut j: usize = 0;
            while j < n {
                if arr[j] == value {
                    count += 1;
                }
                j += 1;
            }

            let mut duplicate_count: bool = false;
            let mut t: usize = 0;
            while t < counts.len() {
                if counts[t] == count {
                    duplicate_count = true;
                    break;
                }
                t += 1;
            }

            if duplicate_count {
                return false;
            }

            counts.push(count);
        }

        i += 1;
    }

    true
}
