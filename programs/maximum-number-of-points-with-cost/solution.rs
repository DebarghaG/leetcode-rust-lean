pub fn max_points(points: &[Vec<i64>]) -> i64 {
    let m = points.len();
    if m == 0 {
        return 0;
    }

    let n = points[0].len();
    if n == 0 {
        return 0;
    }

    let mut prev: Vec<i64> = Vec::new();
    let mut j = 0;
    while j < n {
        prev.push(points[0][j]);
        j = j + 1;
    }

    let mut i = 1;
    while i < m {
        let mut cur: Vec<i64> = Vec::new();

        // Left-to-right pass:
        // cur[j] = max_{k <= j} prev[k] - (j - k)
        j = 0;
        while j < n {
            let mut best = prev[j];
            if j > 0 {
                let cand = cur[j - 1] - 1;
                if cand > best {
                    best = cand;
                }
            }
            cur.push(best);
            j = j + 1;
        }

        // Right-to-left pass:
        // combine with max_{k >= j} prev[k] - (k - j), add current row points.
        let mut right = prev[n - 1];
        let mut k = n;
        while k > 0 {
            k = k - 1;

            if k < n - 1 {
                let cand = right - 1;
                if prev[k] > cand {
                    right = prev[k];
                } else {
                    right = cand;
                }
            }

            let mut best = cur[k];
            if right > best {
                best = right;
            }
            cur[k] = best + points[i][k];
        }

        prev = cur;
        i = i + 1;
    }

    let mut ans = prev[0];
    j = 1;
    while j < n {
        if prev[j] > ans {
            ans = prev[j];
        }
        j = j + 1;
    }

    ans
}
