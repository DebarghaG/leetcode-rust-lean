pub fn num_moves_stones_ii(stones: &[i64]) -> Vec<i64> {
    let n = stones.len();

    let mut a: Vec<i64> = Vec::new();
    let mut idx = 0;
    while idx < n {
        a.push(stones[idx]);
        idx += 1;
    }

    // Selection sort the copied positions.
    let mut i = 0;
    while i < n {
        let mut min_idx = i;
        let mut j = i + 1;
        while j < n {
            if a[j] < a[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        if min_idx != i {
            let tmp = a[i];
            a[i] = a[min_idx];
            a[min_idx] = tmp;
        }
        i += 1;
    }

    if n < 2 {
        let mut ans: Vec<i64> = Vec::new();
        ans.push(0);
        ans.push(0);
        return ans;
    }

    let ni = n as i64;

    // Maximum number of moves.
    let span1 = a[n - 1] - a[1];
    let span2 = a[n - 2] - a[0];
    let max_span = if span1 > span2 { span1 } else { span2 };
    let max_moves = max_span - (ni - 2);

    // Minimum number of moves using a sliding window of width n.
    let mut min_moves = ni;
    let mut left: usize = 0;
    let mut right: usize = 0;

    while right < n {
        while a[right] - a[left] + 1 > ni {
            left += 1;
        }

        let count = (right - left + 1) as i64;
        let span = a[right] - a[left] + 1;

        let candidate = if count == ni - 1 && span == ni - 1 {
            2
        } else {
            ni - count
        };

        if candidate < min_moves {
            min_moves = candidate;
        }

        right += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    ans.push(min_moves);
    ans.push(max_moves);
    ans
}
