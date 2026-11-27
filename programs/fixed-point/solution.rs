pub fn fixed_point(arr: &[i64]) -> i64 {
    let n = arr.len();
    let mut lo: i64 = 0;
    let mut hi: i64 = n as i64 - 1;
    let mut ans: i64 = -1;

    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        let m = mid as usize;
        if arr[m] == mid {
            ans = mid;
            hi = mid - 1;
        } else if arr[m] < mid {
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    ans
}
