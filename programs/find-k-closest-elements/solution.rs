pub fn find_closest_elements(arr: &[i64], k: i64, x: i64) -> Vec<i64> {
    let n = arr.len();
    let kk = k as usize;

    let mut lo: usize = 0;
    let mut hi: usize = n - 1;

    while hi - lo + 1 > kk {
        let left_dist: i64 = if x >= arr[lo] {
            x - arr[lo]
        } else {
            arr[lo] - x
        };

        let right_dist: i64 = if arr[hi] >= x {
            arr[hi] - x
        } else {
            x - arr[hi]
        };

        if left_dist > right_dist {
            lo += 1;
        } else {
            hi -= 1;
        }
    }

    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = lo;
    while i <= hi {
        out.push(arr[i]);
        i += 1;
    }

    out
}
