pub fn max_possible_score(start: &[i64], d: i64) -> i64 {
    let n = start.len();
    if n < 2 {
        return 0;
    }

    let sorted = merge_sort(start);

    let mut minv = sorted[0];
    let mut maxv = sorted[0];
    let mut i: usize = 1;
    while i < n {
        if sorted[i] < minv {
            minv = sorted[i];
        }
        if sorted[i] > maxv {
            maxv = sorted[i];
        }
        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = (maxv - minv) + d;
    let mut ans: i64 = 0;

    while lo <= hi {
        let mid = lo + (hi - lo) / 2;
        if can_place(&sorted, d, mid) {
            ans = mid;
            lo = mid + 1;
        } else {
            hi = mid - 1;
        }
    }

    ans
}

fn merge_sort(xs: &[i64]) -> Vec<i64> {
    let n = xs.len();
    let mut data: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        data.push(xs[i]);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut out: Vec<i64> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if mid + width < n { mid + width } else { n };

            let mut p = left;
            let mut q = mid;

            while p < mid && q < right {
                if data[p] <= data[q] {
                    out.push(data[p]);
                    p += 1;
                } else {
                    out.push(data[q]);
                    q += 1;
                }
            }

            while p < mid {
                out.push(data[p]);
                p += 1;
            }

            while q < right {
                out.push(data[q]);
                q += 1;
            }

            left = right;
        }

        data = out;
        width = width + width;
    }

    data
}

fn can_place(sorted: &[i64], d: i64, gap: i64) -> bool {
    let n = sorted.len();
    if n == 0 {
        return true;
    }

    let mut prev = sorted[0];
    let mut i: usize = 1;

    while i < n {
        let s = sorted[i];
        let need = prev + gap;
        let mut chosen = s;

        if chosen < need {
            chosen = need;
        }

        let upper = s + d;
        if chosen > upper {
            return false;
        }

        prev = chosen;
        i += 1;
    }

    true
}
