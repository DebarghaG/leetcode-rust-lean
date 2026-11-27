pub fn replace_elements(arr: &[i64]) -> Vec<i64> {
    let n = arr.len();
    let mut out: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < n {
        out.push(0);
        k = k + 1;
    }

    let mut max_right: i64 = -1;
    let mut i: usize = n;

    while i > 0 {
        i = i - 1;
        let current = arr[i];
        out[i] = max_right;
        if current > max_right {
            max_right = current;
        }
    }

    out
}
