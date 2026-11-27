pub fn beautiful_array(n: i64) -> Vec<i64> {
    let mut arr: Vec<i64> = Vec::new();
    arr.push(1);

    let mut steps: i64 = 0;
    while steps < 10 {
        let mut next: Vec<i64> = Vec::new();

        let mut i: usize = 0;
        while i < arr.len() {
            let x = arr[i];
            next.push(2 * x - 1);
            i += 1;
        }

        let mut j: usize = 0;
        while j < arr.len() {
            let x = arr[j];
            next.push(2 * x);
            j += 1;
        }

        arr = next;
        steps += 1;
    }

    let mut res: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < arr.len() {
        if arr[k] <= n {
            res.push(arr[k]);
        }
        k += 1;
    }

    res
}
