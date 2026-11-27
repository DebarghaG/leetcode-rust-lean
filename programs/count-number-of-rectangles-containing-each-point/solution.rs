fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut width: usize = 1;
    while width < n {
        let mut tmp: Vec<i64> = Vec::new();
        let mut start: usize = 0;

        while start < n {
            let mid_add = start + width;
            let mid: usize = if mid_add < n { mid_add } else { n };

            let end_add = start + width + width;
            let end: usize = if end_add < n { end_add } else { n };

            let mut i = start;
            let mut j = mid;

            while i < mid && j < end {
                if v[i] <= v[j] {
                    tmp.push(v[i]);
                    i += 1;
                } else {
                    tmp.push(v[j]);
                    j += 1;
                }
            }

            while i < mid {
                tmp.push(v[i]);
                i += 1;
            }

            while j < end {
                tmp.push(v[j]);
                j += 1;
            }

            start = end;
        }

        let mut k: usize = 0;
        while k < n {
            v[k] = tmp[k];
            k += 1;
        }

        width = width * 2;
    }
}

fn merge_sorted(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let an = a.len();
    let bn = b.len();

    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < an && j < bn {
        if a[i] <= b[j] {
            out.push(a[i]);
            i += 1;
        } else {
            out.push(b[j]);
            j += 1;
        }
    }

    while i < an {
        out.push(a[i]);
        i += 1;
    }

    while j < bn {
        out.push(b[j]);
        j += 1;
    }

    out
}

fn lower_bound(v: &Vec<i64>, target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = v.len();

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

pub fn count_rectangles(rectangles: &[Vec<i64>], points: &[Vec<i64>]) -> Vec<i64> {
    let mut buckets: Vec<Vec<i64>> = Vec::new();
    let mut hinit: usize = 0;
    while hinit <= 100 {
        buckets.push(Vec::new());
        hinit += 1;
    }

    let mut r: usize = 0;
    while r < rectangles.len() {
        let length = rectangles[r][0];
        let height = rectangles[r][1];

        if height >= 1 && height <= 100 {
            let hi = height as usize;
            buckets[hi].push(length);
        }

        r += 1;
    }

    let mut h: usize = 0;
    while h <= 100 {
        sort_i64(&mut buckets[h]);
        h += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut p: usize = 0;
    while p < points.len() {
        ans.push(0);
        p += 1;
    }

    let mut cumulative: Vec<i64> = Vec::new();

    let mut y: usize = 100;
    while y > 0 {
        let merged = merge_sorted(&cumulative, &buckets[y]);
        cumulative = merged;

        let mut q: usize = 0;
        while q < points.len() {
            if points[q][1] == y as i64 {
                let x = points[q][0];
                let pos = lower_bound(&cumulative, x);
                let count = cumulative.len() - pos;
                ans[q] = count as i64;
            }
            q += 1;
        }

        y -= 1;
    }

    ans
}
