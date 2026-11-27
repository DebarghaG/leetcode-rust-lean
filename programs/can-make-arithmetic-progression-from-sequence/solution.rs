pub fn can_make_arithmetic_progression(arr: &[i64]) -> bool {
    let n = arr.len();

    if n < 2 {
        return true;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(arr[i]);
        i += 1;
    }

    // Insertion sort the copied elements in nondecreasing order.
    let mut i: usize = 1;
    while i < n {
        let key = v[i];
        let mut j: usize = i;

        while j > 0 {
            if v[j - 1] > key {
                v[j] = v[j - 1];
                j -= 1;
            } else {
                break;
            }
        }

        v[j] = key;
        i += 1;
    }

    let diff = v[1] - v[0];
    let mut k: usize = 2;
    while k < n {
        if v[k] - v[k - 1] != diff {
            return false;
        }
        k += 1;
    }

    true
}
