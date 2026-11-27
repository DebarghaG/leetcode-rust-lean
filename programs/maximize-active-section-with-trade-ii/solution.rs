fn range_max(tree: &[i64], size: usize, l: usize, r: usize) -> i64 {
    let mut res: i64 = 0;
    let mut left = l + size;
    let mut right = r + size + 1;

    while left < right {
        if left % 2 == 1 {
            if tree[left] > res {
                res = tree[left];
            }
            left += 1;
        }
        if right % 2 == 1 {
            right -= 1;
            if tree[right] > res {
                res = tree[right];
            }
        }
        left /= 2;
        right /= 2;
    }

    res
}

pub fn max_active_sections_after_trade(s: &[u8], queries: &[Vec<i64>]) -> Vec<i64> {
    let n = s.len();
    let mut total: i64 = 0;

    let mut starts: Vec<i64> = Vec::new();
    let mut ends: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        if s[i] == b'1' {
            let a = i as i64;
            let mut j = i;
            while j < n {
                if s[j] == b'1' {
                    j += 1;
                } else {
                    break;
                }
            }
            let b = (j - 1) as i64;
            starts.push(a);
            ends.push(b);
            total = total + (b - a + 1);
            i = j;
        } else {
            i += 1;
        }
    }

    let m = starts.len();
    let qn = queries.len();

    if m == 0 {
        let mut ans: Vec<i64> = Vec::new();
        let mut qi: usize = 0;
        while qi < qn {
            ans.push(0);
            qi += 1;
        }
        return ans;
    }

    let mut lefts: Vec<i64> = Vec::new();
    let mut rights: Vec<i64> = Vec::new();

    let mut k: usize = 0;
    while k < m {
        if k == 0 {
            lefts.push(starts[k]);
        } else {
            lefts.push(starts[k] - ends[k - 1] - 1);
        }
        k += 1;
    }

    k = 0;
    while k < m {
        if k + 1 == m {
            rights.push((n as i64 - 1) - ends[k]);
        } else {
            rights.push(starts[k + 1] - ends[k] - 1);
        }
        k += 1;
    }

    let mut size: usize = 1;
    while size < m {
        size = size * 2;
    }

    let mut tree: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < 2 * size {
        tree.push(0);
        idx += 1;
    }

    k = 0;
    while k < m {
        tree[size + k] = lefts[k] + rights[k];
        k += 1;
    }

    let mut node: usize = size;
    while node > 1 {
        node -= 1;
        let lv = tree[2 * node];
        let rv = tree[2 * node + 1];
        if lv > rv {
            tree[node] = lv;
        } else {
            tree[node] = rv;
        }
    }

    let mut ans: Vec<i64> = Vec::new();
    let mut qi: usize = 0;

    while qi < qn {
        let l = queries[qi][0];
        let r = queries[qi][1];

        let mut p_lo: usize = 0;
        let mut p_hi: usize = m;
        while p_lo < p_hi {
            let mid = (p_lo + p_hi) / 2;
            if starts[mid] > l {
                p_hi = mid;
            } else {
                p_lo = mid + 1;
            }
        }
        let p = p_lo;

        let mut ub_lo: usize = 0;
        let mut ub_hi: usize = m;
        while ub_lo < ub_hi {
            let mid = (ub_lo + ub_hi) / 2;
            if ends[mid] >= r {
                ub_hi = mid;
            } else {
                ub_lo = mid + 1;
            }
        }
        let ub = ub_lo;

        let mut best: i64 = 0;

        if p < ub {
            let q = ub - 1;

            let ap = starts[p];
            let bp = ends[p];

            let mut left_term = lefts[p];
            let dl = ap - l;
            if dl < left_term {
                left_term = dl;
            }

            let mut right_term = rights[p];
            let dr = r - bp;
            if dr < right_term {
                right_term = dr;
            }

            best = left_term + right_term;

            if p < q {
                let aq = starts[q];
                let bq = ends[q];

                let mut left_q = lefts[q];
                let dlq = aq - l;
                if dlq < left_q {
                    left_q = dlq;
                }

                let mut right_q = rights[q];
                let drq = r - bq;
                if drq < right_q {
                    right_q = drq;
                }

                let cand_q = left_q + right_q;
                if cand_q > best {
                    best = cand_q;
                }

                let inner_l = p + 1;
                let inner_r = q - 1;

                if inner_l <= inner_r {
                    let im = range_max(&tree, size, inner_l, inner_r);
                    if im > best {
                        best = im;
                    }
                }
            }
        }

        ans.push(total + best);
        qi += 1;
    }

    ans
}
