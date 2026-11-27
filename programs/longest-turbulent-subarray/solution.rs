pub fn max_turbulence_size(arr: &[i64]) -> i64 {
    let n = arr.len();
    if n == 0 {
        return 0;
    }

    let mut up: i64 = 1;
    let mut down: i64 = 1;
    let mut best: i64 = 1;

    let mut i: usize = 1;
    while i < n {
        if arr[i - 1] < arr[i] {
            up = down + 1;
            down = 1;
        } else if arr[i - 1] > arr[i] {
            down = up + 1;
            up = 1;
        } else {
            up = 1;
            down = 1;
        }

        if up > best {
            best = up;
        }
        if down > best {
            best = down;
        }

        i += 1;
    }

    best
}
