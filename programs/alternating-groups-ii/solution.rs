pub fn number_of_alternating_groups(colors: &[i64], k: i64) -> i64 {
    let n = colors.len();
    let m = (k - 1) as usize;

    let mut edges: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let next = if i + 1 < n { i + 1 } else { 0 };
        if colors[i] != colors[next] {
            edges.push(1);
        } else {
            edges.push(0);
        }
        i += 1;
    }

    let mut window_sum: i64 = 0;
    let mut j: usize = 0;
    while j < m {
        window_sum += edges[j];
        j += 1;
    }

    let mut count: i64 = 0;
    let mut start: usize = 0;
    while start < n {
        if window_sum == (m as i64) {
            count += 1;
        }

        window_sum -= edges[start];

        let mut add_index = start + m;
        if add_index >= n {
            add_index -= n;
        }
        window_sum += edges[add_index];

        start += 1;
    }

    count
}
