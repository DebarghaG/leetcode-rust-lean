pub fn get_last_moment(n: i64, left: &[i64], right: &[i64]) -> i64 {
    let mut ans: i64 = 0;

    let mut i: usize = 0;
    while i < left.len() {
        if left[i] > ans {
            ans = left[i];
        }
        i += 1;
    }

    let mut j: usize = 0;
    while j < right.len() {
        let t: i64 = n - right[j];
        if t > ans {
            ans = t;
        }
        j += 1;
    }

    ans
}
