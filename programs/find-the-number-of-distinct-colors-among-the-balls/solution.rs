fn lower_bound(a: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = a.len();
    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if a[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn unique_sorted(mut v: Vec<i64>) -> Vec<i64> {
    v.sort();
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < v.len() {
        if i == 0 || v[i] != v[i - 1] {
            out.push(v[i]);
        }
        i += 1;
    }
    out
}

pub fn query_results(limit: i64, queries: &[Vec<i64>]) -> Vec<i64> {
    let _ = limit;

    let n: usize = queries.len();

    let mut ball_vals: Vec<i64> = Vec::new();
    let mut color_vals: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        ball_vals.push(queries[i][0]);
        color_vals.push(queries[i][1]);
        i += 1;
    }

    let ball_keys: Vec<i64> = unique_sorted(ball_vals);
    let color_keys: Vec<i64> = unique_sorted(color_vals);

    let ball_count: usize = ball_keys.len();
    let color_key_count: usize = color_keys.len();

    let mut ball_color: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j < ball_count {
        ball_color.push(-1);
        j += 1;
    }

    let mut color_count: Vec<i64> = Vec::new();
    j = 0;
    while j < color_key_count {
        color_count.push(0);
        j += 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut distinct: i64 = 0;

    i = 0;
    while i < n {
        let ball: i64 = queries[i][0];
        let color: i64 = queries[i][1];

        let bi: usize = lower_bound(&ball_keys, ball);
        let ci: usize = lower_bound(&color_keys, color);

        let old_color: i64 = ball_color[bi];

        if old_color != -1 {
            let old_idx: usize = old_color as usize;
            color_count[old_idx] = color_count[old_idx] - 1;
            if color_count[old_idx] == 0 {
                distinct -= 1;
            }
        }

        ball_color[bi] = ci as i64;

        if color_count[ci] == 0 {
            distinct += 1;
        }
        color_count[ci] = color_count[ci] + 1;

        result.push(distinct);
        i += 1;
    }

    result
}
