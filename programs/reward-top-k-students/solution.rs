fn cmp_dict_word(dict: &[Vec<u8>], i: usize, j: usize) -> i64 {
    let li = dict[i].len();
    let lj = dict[j].len();
    let mut t = 0;
    while t < li && t < lj {
        let a = dict[i][t];
        let b = dict[j][t];
        if a < b {
            return -1;
        }
        if a > b {
            return 1;
        }
        t += 1;
    }
    if li < lj {
        return -1;
    }
    if li > lj {
        return 1;
    }
    0
}

fn build_sorted_order(dict: &[Vec<u8>]) -> Vec<usize> {
    let n = dict.len();
    let mut order: Vec<usize> = Vec::new();
    let mut aux: Vec<usize> = Vec::new();

    let mut i = 0;
    while i < n {
        order.push(i);
        aux.push(0);
        i += 1;
    }

    let mut width = 1;
    while width < n {
        let mut left = 0;
        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }
            let mut right = left + 2 * width;
            if right > n {
                right = n;
            }

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                let cmp = cmp_dict_word(dict, order[a], order[b]);
                if cmp <= 0 {
                    aux[k] = order[a];
                    a += 1;
                } else {
                    aux[k] = order[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                aux[k] = order[a];
                a += 1;
                k += 1;
            }

            while b < right {
                aux[k] = order[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        let mut t = 0;
        while t < n {
            order[t] = aux[t];
            t += 1;
        }

        width = width * 2;
    }

    order
}

fn cmp_report_segment_word(
    report: &[Vec<u8>],
    ri: usize,
    start: usize,
    end: usize,
    dict: &[Vec<u8>],
    di: usize,
) -> i64 {
    let sl = end - start;
    let dl = dict[di].len();
    let mut t = 0;

    while t < sl && t < dl {
        let a = report[ri][start + t];
        let b = dict[di][t];
        if a < b {
            return -1;
        }
        if a > b {
            return 1;
        }
        t += 1;
    }

    if sl < dl {
        return -1;
    }
    if sl > dl {
        return 1;
    }
    0
}

fn student_better(points: &[i64], ids: &[i64], a: usize, b: usize) -> bool {
    if points[a] > points[b] {
        return true;
    }
    if points[a] < points[b] {
        return false;
    }
    ids[a] < ids[b]
}

fn build_rank_order(points: &[i64], ids: &[i64]) -> Vec<usize> {
    let n = points.len();
    let mut order: Vec<usize> = Vec::new();
    let mut aux: Vec<usize> = Vec::new();

    let mut i = 0;
    while i < n {
        order.push(i);
        aux.push(0);
        i += 1;
    }

    let mut width = 1;
    while width < n {
        let mut left = 0;
        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }
            let mut right = left + 2 * width;
            if right > n {
                right = n;
            }

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if student_better(points, ids, order[a], order[b]) {
                    aux[k] = order[a];
                    a += 1;
                } else {
                    aux[k] = order[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                aux[k] = order[a];
                a += 1;
                k += 1;
            }

            while b < right {
                aux[k] = order[b];
                b += 1;
                k += 1;
            }

            left = right;
        }

        let mut t = 0;
        while t < n {
            order[t] = aux[t];
            t += 1;
        }

        width = width * 2;
    }

    order
}

pub fn top_students(
    positive_feedback: &[Vec<u8>],
    negative_feedback: &[Vec<u8>],
    report: &[Vec<u8>],
    student_id: &[i64],
    k: i64,
) -> Vec<i64> {
    let pos_order = build_sorted_order(positive_feedback);
    let neg_order = build_sorted_order(negative_feedback);

    let n = report.len();
    let mut points: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        points.push(0);
        i += 1;
    }

    i = 0;
    while i < n {
        let len = report[i].len();
        let mut p = 0;

        while p < len {
            while p < len && report[i][p] == b' ' {
                p += 1;
            }

            let start = p;

            while p < len && report[i][p] != b' ' {
                p += 1;
            }

            let end = p;

            if start < end {
                let mut found_pos = false;
                let mut lo = 0;
                let mut hi = pos_order.len();

                while lo < hi {
                    let mid = (lo + hi) / 2;
                    let cmp = cmp_report_segment_word(
                        report,
                        i,
                        start,
                        end,
                        positive_feedback,
                        pos_order[mid],
                    );

                    if cmp == 0 {
                        found_pos = true;
                        break;
                    }

                    if cmp < 0 {
                        hi = mid;
                    } else {
                        lo = mid + 1;
                    }
                }

                if found_pos {
                    points[i] += 3;
                } else {
                    let mut found_neg = false;
                    lo = 0;
                    hi = neg_order.len();

                    while lo < hi {
                        let mid = (lo + hi) / 2;
                        let cmp = cmp_report_segment_word(
                            report,
                            i,
                            start,
                            end,
                            negative_feedback,
                            neg_order[mid],
                        );

                        if cmp == 0 {
                            found_neg = true;
                            break;
                        }

                        if cmp < 0 {
                            hi = mid;
                        } else {
                            lo = mid + 1;
                        }
                    }

                    if found_neg {
                        points[i] -= 1;
                    }
                }
            }
        }

        i += 1;
    }

    let order = build_rank_order(&points, student_id);

    let mut ans: Vec<i64> = Vec::new();
    let mut remaining = k;
    let mut t = 0;

    while t < order.len() && remaining > 0 {
        ans.push(student_id[order[t]]);
        t += 1;
        remaining -= 1;
    }

    ans
}
