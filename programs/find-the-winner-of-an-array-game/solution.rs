pub fn get_winner(arr: &[i64], k: i64) -> i64 {
    let n = arr.len();
    let mut current: i64 = arr[0];
    let mut wins: i64 = 0;
    let mut i: usize = 1;

    while i < n {
        if arr[i] < current {
            wins = wins + 1;
        } else {
            current = arr[i];
            wins = 1;
        }

        if wins == k {
            return current;
        }

        i = i + 1;
    }

    current
}
