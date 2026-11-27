pub fn find_lucky(arr: &[i64]) -> i64 {
    let mut counts: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < 502 {
        counts.push(0);
        k += 1;
    }

    let mut i: usize = 0;
    while i < arr.len() {
        let v = arr[i];
        if v >= 1 && v <= 500 {
            let idx = v as usize;
            counts[idx] = counts[idx] + 1;
        }
        i += 1;
    }

    let mut x: usize = 500;
    while x > 0 {
        let xv = x as i64;
        if counts[x] == xv {
            return xv;
        }
        x -= 1;
    }

    -1
}
