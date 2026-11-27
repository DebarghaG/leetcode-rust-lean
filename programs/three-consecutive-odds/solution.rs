pub fn three_consecutive_odds(arr: &[i64]) -> bool {
    let n = arr.len();
    if n < 3 {
        return false;
    }
    let mut i: usize = 0;
    while i + 2 < n {
        let a = arr[i];
        let b = arr[i + 1];
        let c = arr[i + 2];
        let odd_a = a % 2 != 0;
        let odd_b = b % 2 != 0;
        let odd_c = c % 2 != 0;
        if odd_a && odd_b && odd_c {
            return true;
        }
        i += 1;
    }
    false
}
