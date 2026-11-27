fn zeros(n: usize) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(0i64);
        i += 1;
    }
    v
}

fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut tmp: Vec<i64> = zeros(n);
    let mut width: usize = 1;

    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid: usize = if left + width < n { left + width } else { n };
            let bound: usize = if left + 2 * width < n {
                left + 2 * width
            } else {
                n
            };

            let mut i = left;
            let mut j = mid;
            let mut k = left;

            while i < mid && j < bound {
                if v[i] <= v[j] {
                    tmp[k] = v[i];
                    i += 1;
                } else {
                    tmp[k] = v[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                tmp[k] = v[i];
                i += 1;
                k += 1;
            }

            while j < bound {
                tmp[k] = v[j];
                j += 1;
                k += 1;
            }

            left = bound;
        }

        let mut idx: usize = 0;
        while idx < n {
            v[idx] = tmp[idx];
            idx += 1;
        }

        width = width * 2;
    }
}

fn bit_add(tree: &mut Vec<i64>, mut idx: usize, delta: i64) {
    if idx == 0 {
        return;
    }

    let n = tree.len();
    while idx < n {
        tree[idx] = tree[idx] + delta;
        let low = idx & (!idx + 1);
        idx += low;
    }
}

fn bit_sum(tree: &Vec<i64>, mut idx: usize) -> i64 {
    let mut s: i64 = 0;
    while idx > 0 {
        s += tree[idx];
        let low = idx & (!idx + 1);
        idx -= low;
    }
    s
}

fn bit_find_prefix_leq(tree: &Vec<i64>, q: i64) -> usize {
    let n = tree.len() - 1;
    let mut idx: usize = 0;
    let mut acc: i64 = 0;

    let mut step: usize = 1;
    while step <= n {
        step <<= 1;
    }
    step >>= 1;

    while step > 0 {
        let next = idx + step;
        if next <= n && acc + tree[next] <= q {
            idx = next;
            acc += tree[next];
        }
        step >>= 1;
    }

    idx
}

fn find_pos(coords: &Vec<i64>, target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = coords.len();

    while lo < hi {
        let mid = (lo + hi) / 2;
        if coords[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

fn update_value(
    ci: usize,
    v: i64,
    delta: i64,
    cnt: &mut Vec<i64>,
    freq_num: &mut Vec<i64>,
    freq_weight: &mut Vec<i64>,
    per_count: &mut Vec<Vec<i64>>,
    per_sum: &mut Vec<Vec<i64>>,
    freq_coords: &Vec<Vec<i64>>,
    distinct: &mut i64,
    window_sum: &mut i64,
) {
    let old = cnt[ci];
    let new = old + delta;

    if old > 0 {
        let f = old as usize;
        bit_add(freq_num, f, -1);
        bit_add(freq_weight, f, -old * v);

        let p = find_pos(&freq_coords[f], v) + 1;
        bit_add(&mut per_count[f], p, -1);
        bit_add(&mut per_sum[f], p, -v);
    }

    if new > 0 {
        let f = new as usize;
        bit_add(freq_num, f, 1);
        bit_add(freq_weight, f, new * v);

        let p = find_pos(&freq_coords[f], v) + 1;
        bit_add(&mut per_count[f], p, 1);
        bit_add(&mut per_sum[f], p, v);
    }

    if old == 0 && new > 0 {
        *distinct = *distinct + 1;
    }
    if old > 0 && new == 0 {
        *distinct = *distinct - 1;
    }

    *window_sum = *window_sum + delta * v;
    cnt[ci] = new;
}

fn compute_x_sum(
    x: usize,
    _kk: usize,
    distinct: i64,
    window_sum: i64,
    freq_num: &Vec<i64>,
    freq_weight: &Vec<i64>,
    per_count: &Vec<Vec<i64>>,
    per_sum: &Vec<Vec<i64>>,
    freq_coords: &Vec<Vec<i64>>,
) -> i64 {
    let x_i = x as i64;

    if distinct <= x_i {
        return window_sum;
    }

    let r_total = distinct - x_i;
    let idx = bit_find_prefix_leq(freq_num, r_total);
    let t = idx + 1;

    if t == 0 {
        return window_sum;
    }

    let prefix_t = bit_sum(freq_num, t);
    let prefix_prev = bit_sum(freq_num, t - 1);
    let selected_above = distinct - prefix_t;
    let r = x_i - selected_above;

    let prefix_weight_t = bit_sum(freq_weight, t);
    let sum_above = window_sum - prefix_weight_t;

    let num_t = prefix_t - prefix_prev;
    let q = num_t - r;

    let len_t = per_sum[t].len();
    if len_t == 0 {
        return window_sum;
    }

    let total_values_t = bit_sum(&per_sum[t], len_t - 1);
    let mut small_sum: i64 = 0;

    if q > 0 {
        let pos = bit_find_prefix_leq(&per_count[t], q - 1);
        let p = pos + 1;
        let before = bit_sum(&per_sum[t], pos);
        let next_val = freq_coords[t][p - 1];
        small_sum = before + next_val;
    }

    let large_values_sum = total_values_t - small_sum;
    sum_above + (t as i64) * large_values_sum
}

pub fn find_x_sum(nums: &[i64], k: i64, x: i64) -> Vec<i64> {
    let n = nums.len();
    if n == 0 {
        return Vec::new();
    }

    let kk = k as usize;
    let xx = x as usize;

    if kk == 0 {
        return Vec::new();
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }
    sort_i64(&mut sorted);

    let mut vals: Vec<i64> = Vec::new();
    i = 0;
    while i < n {
        let v = sorted[i];
        vals.push(v);
        i += 1;
        while i < n && sorted[i] == v {
            i += 1;
        }
    }

    let m = vals.len();
    let mut comp: Vec<i64> = zeros(n);

    i = 0;
    while i < n {
        let idx = find_pos(&vals, nums[i]);
        comp[i] = idx as i64;
        i += 1;
    }

    let mut freq_lists: Vec<Vec<i64>> = Vec::new();
    let mut f: usize = 0;
    while f <= kk + 1 {
        freq_lists.push(Vec::new());
        f += 1;
    }

    let mut pre_cnt: Vec<i64> = zeros(m);

    i = 0;
    while i < kk {
        let ci = comp[i] as usize;
        let v = vals[ci];
        let old = pre_cnt[ci];
        let new = old + 1;

        if old > 0 {
            freq_lists[old as usize].push(v);
        }
        if new > 0 {
            freq_lists[new as usize].push(v);
        }

        pre_cnt[ci] = new;
        i += 1;
    }

    let mut s: usize = 0;
    while s + kk < n {
        let ci = comp[s] as usize;
        let v = vals[ci];
        let old = pre_cnt[ci];
        let new = old - 1;

        if old > 0 {
            freq_lists[old as usize].push(v);
        }
        if new > 0 {
            freq_lists[new as usize].push(v);
        }

        pre_cnt[ci] = new;

        let in_idx = s + kk;
        let ci2 = comp[in_idx] as usize;
        let v2 = vals[ci2];
        let old2 = pre_cnt[ci2];
        let new2 = old2 + 1;

        if old2 > 0 {
            freq_lists[old2 as usize].push(v2);
        }
        if new2 > 0 {
            freq_lists[new2 as usize].push(v2);
        }

        pre_cnt[ci2] = new2;
        s += 1;
    }

    f = 1;
    while f <= kk {
        sort_i64(&mut freq_lists[f]);

        let len = freq_lists[f].len();
        let mut uniq: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        let mut have_prev = false;
        let mut prev: i64 = 0;

        while j < len {
            let v = freq_lists[f][j];
            if !have_prev || v != prev {
                uniq.push(v);
                prev = v;
                have_prev = true;
            }
            j += 1;
        }

        freq_lists[f] = uniq;
        f += 1;
    }

    let mut per_count: Vec<Vec<i64>> = Vec::new();
    let mut per_sum: Vec<Vec<i64>> = Vec::new();

    f = 0;
    while f <= kk + 1 {
        let len = freq_lists[f].len();
        if len == 0 {
            per_count.push(Vec::new());
            per_sum.push(Vec::new());
        } else {
            per_count.push(zeros(len + 1));
            per_sum.push(zeros(len + 1));
        }
        f += 1;
    }

    let mut cnt: Vec<i64> = zeros(m);
    let mut freq_num: Vec<i64> = zeros(kk + 2);
    let mut freq_weight: Vec<i64> = zeros(kk + 2);

    let mut distinct: i64 = 0;
    let mut window_sum: i64 = 0;

    i = 0;
    while i < kk {
        let ci = comp[i] as usize;
        let v = vals[ci];
        update_value(
            ci,
            v,
            1,
            &mut cnt,
            &mut freq_num,
            &mut freq_weight,
            &mut per_count,
            &mut per_sum,
            &freq_lists,
            &mut distinct,
            &mut window_sum,
        );
        i += 1;
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut start: usize = 0;

    while start + kk <= n {
        let res = compute_x_sum(
            xx,
            kk,
            distinct,
            window_sum,
            &freq_num,
            &freq_weight,
            &per_count,
            &per_sum,
            &freq_lists,
        );
        ans.push(res);

        if start + kk < n {
            let out_idx = start;
            let ci = comp[out_idx] as usize;
            let v = vals[ci];
            update_value(
                ci,
                v,
                -1,
                &mut cnt,
                &mut freq_num,
                &mut freq_weight,
                &mut per_count,
                &mut per_sum,
                &freq_lists,
                &mut distinct,
                &mut window_sum,
            );

            let in_idx = start + kk;
            let ci2 = comp[in_idx] as usize;
            let v2 = vals[ci2];
            update_value(
                ci2,
                v2,
                1,
                &mut cnt,
                &mut freq_num,
                &mut freq_weight,
                &mut per_count,
                &mut per_sum,
                &freq_lists,
                &mut distinct,
                &mut window_sum,
            );
        }

        start += 1;
    }

    ans
}
