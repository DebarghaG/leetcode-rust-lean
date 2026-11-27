pub fn longest_common_subpath(n: i64, paths: &[Vec<i64>]) -> i64 {
    let m = paths.len();
    if m == 0 {
        return 0;
    }

    let mut min_len: i64 = paths[0].len() as i64;
    let mut i: usize = 1;
    while i < m {
        let l = paths[i].len() as i64;
        if l < min_len {
            min_len = l;
        }
        i += 1;
    }
    if min_len == 0 {
        return 0;
    }

    let mut arr: Vec<i64> = Vec::new();
    let mut path_id: Vec<i64> = Vec::new();

    i = 0;
    while i < m {
        let row = &paths[i];
        let mut j: usize = 0;
        while j < row.len() {
            arr.push(row[j] + 1);
            path_id.push(i as i64);
            j += 1;
        }
        if i + 1 < m {
            arr.push(n + 2 + (i as i64));
            path_id.push(-1);
        }
        i += 1;
    }

    let orig_len = arr.len();
    if orig_len == 0 {
        return 0;
    }
    arr.push(0);

    let sa = build_suffix_array(&arr);

    let mut rank: Vec<usize> = Vec::new();
    i = 0;
    while i < orig_len {
        rank.push(0);
        i += 1;
    }
    i = 0;
    while i < orig_len {
        rank[sa[i]] = i;
        i += 1;
    }

    let mut lcp: Vec<usize> = Vec::new();
    i = 0;
    while i < orig_len {
        lcp.push(0);
        i += 1;
    }

    let mut h: usize = 0;
    i = 0;
    while i < orig_len {
        let r = rank[i];
        if r > 0 {
            let j = sa[r - 1];
            while i + h < orig_len && j + h < orig_len && arr[i + h] == arr[j + h] {
                h += 1;
            }
            lcp[r] = h;
            if h > 0 {
                h -= 1;
            }
        } else {
            h = 0;
        }
        i += 1;
    }

    let mut colors: Vec<i64> = Vec::new();
    let mut between: Vec<i64> = Vec::new();
    let inf: i64 = orig_len as i64 + 1;
    let mut prev_rank: i64 = -1;
    let mut cur_min: i64 = inf;

    i = 0;
    while i < orig_len {
        if i > 0 && prev_rank >= 0 {
            let v = lcp[i] as i64;
            if v < cur_min {
                cur_min = v;
            }
        }

        let pos = sa[i];
        let pid = path_id[pos];
        if pid >= 0 {
            colors.push(pid);
            if prev_rank >= 0 {
                between.push(cur_min);
            } else {
                between.push(0);
            }
            prev_rank = i as i64;
            cur_min = inf;
        }

        i += 1;
    }

    let mut lo: i64 = 0;
    let mut hi: i64 = min_len;
    while lo < hi {
        let mid = lo + (hi - lo + 1) / 2;
        if check(m, &colors, &between, mid) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }

    lo
}

fn check(m: usize, colors: &[i64], between: &[i64], len: i64) -> bool {
    if len == 0 {
        return true;
    }

    let vlen = colors.len();
    if vlen == 0 {
        return false;
    }

    let mut cnt: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < m {
        cnt.push(0);
        i += 1;
    }

    let target = m as i64;
    let mut distinct: i64 = 0;
    let mut pos: usize = 0;

    while pos < vlen {
        let start = pos;

        let c0 = colors[pos] as usize;
        if cnt[c0] == 0 {
            distinct += 1;
        }
        cnt[c0] += 1;

        let mut j = pos + 1;
        while j < vlen && between[j] >= len {
            let c = colors[j] as usize;
            if cnt[c] == 0 {
                distinct += 1;
            }
            cnt[c] += 1;
            j += 1;
        }

        if distinct == target {
            return true;
        }

        let mut k = start;
        while k < j {
            let c = colors[k] as usize;
            cnt[c] = 0;
            k += 1;
        }

        distinct = 0;
        pos = j;
    }

    false
}

fn build_suffix_array(data: &[i64]) -> Vec<usize> {
    let n = data.len();
    let mut out: Vec<usize> = Vec::new();
    if n <= 1 {
        return out;
    }

    let mut maxv: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if data[i] > maxv {
            maxv = data[i];
        }
        i += 1;
    }

    let alphabet = (maxv as usize) + 1;
    let mut cnt: Vec<usize> = Vec::new();
    i = 0;
    while i < alphabet {
        cnt.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let v = data[i] as usize;
        cnt[v] += 1;
        i += 1;
    }

    i = 1;
    while i < alphabet {
        cnt[i] += cnt[i - 1];
        i += 1;
    }

    let mut p: Vec<usize> = Vec::new();
    i = 0;
    while i < n {
        p.push(0);
        i += 1;
    }

    i = n;
    while i > 0 {
        i -= 1;
        let v = data[i] as usize;
        cnt[v] -= 1;
        p[cnt[v]] = i;
    }

    let mut c: Vec<usize> = Vec::new();
    i = 0;
    while i < n {
        c.push(0);
        i += 1;
    }

    let mut classes: usize = 1;
    c[p[0]] = 0;
    i = 1;
    while i < n {
        if data[p[i]] != data[p[i - 1]] {
            classes += 1;
        }
        c[p[i]] = classes - 1;
        i += 1;
    }

    let mut shift: usize = 1;
    while shift < n {
        let mut pn: Vec<usize> = Vec::new();
        i = 0;
        while i < n {
            pn.push(0);
            i += 1;
        }

        i = 0;
        while i < n {
            let v = p[i];
            if v >= shift {
                pn[i] = v - shift;
            } else {
                pn[i] = v + n - shift;
            }
            i += 1;
        }

        let mut cnt2: Vec<usize> = Vec::new();
        i = 0;
        while i < classes {
            cnt2.push(0);
            i += 1;
        }

        i = 0;
        while i < n {
            let cl = c[pn[i]];
            cnt2[cl] += 1;
            i += 1;
        }

        i = 1;
        while i < classes {
            cnt2[i] += cnt2[i - 1];
            i += 1;
        }

        i = n;
        while i > 0 {
            i -= 1;
            let cl = c[pn[i]];
            cnt2[cl] -= 1;
            p[cnt2[cl]] = pn[i];
        }

        let mut cn: Vec<usize> = Vec::new();
        i = 0;
        while i < n {
            cn.push(0);
            i += 1;
        }

        cn[p[0]] = 0;
        let mut new_classes: usize = 1;
        i = 1;
        while i < n {
            let cur = p[i];
            let prev = p[i - 1];

            let cur_plus = cur + shift;
            let prev_plus = prev + shift;
            let cur_second = if cur_plus >= n { cur_plus - n } else { cur_plus };
            let prev_second = if prev_plus >= n { prev_plus - n } else { prev_plus };

            if c[cur] != c[prev] || c[cur_second] != c[prev_second] {
                new_classes += 1;
            }
            cn[cur] = new_classes - 1;
            i += 1;
        }

        c = cn;
        classes = new_classes;
        shift = shift * 2;
    }

    i = 1;
    while i < n {
        out.push(p[i]);
        i += 1;
    }

    out
}
