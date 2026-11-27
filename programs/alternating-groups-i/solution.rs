pub fn number_of_alternating_groups(colors: &[i64]) -> i64 {
    let n: usize = colors.len();
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let left_index: usize = if i == 0 { n - 1 } else { i - 1 };
        let right_index: usize = if i + 1 == n { 0 } else { i + 1 };

        let left: i64 = colors[left_index];
        let middle: i64 = colors[i];
        let right: i64 = colors[right_index];

        if middle != left && middle != right {
            count += 1;
        }

        i += 1;
    }

    count
}
