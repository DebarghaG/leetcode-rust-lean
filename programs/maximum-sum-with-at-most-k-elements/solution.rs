pub fn max_sum(grid: &[Vec<i64>], limits: &[i64], k: i64) -> i64 {
    let n = grid.len();
    let mut candidates: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let row = &grid[i];
        let m = row.len();

        // Compute m as i64 and find the maximum value in this row.
        let mut m_i64: i64 = 0;
        let mut max_val: i64 = 0;
        let mut j = 0;
        while j < m {
            if row[j] > max_val {
                max_val = row[j];
            }
            m_i64 += 1;
            j += 1;
        }

        // Determine the limit for this row.
        let mut lim: i64 = 0;
        if i < limits.len() {
            lim = limits[i];
        }
        if lim > m_i64 {
            lim = m_i64;
        }

        if lim > 0 && m > 0 {
            // Binary search for the threshold value T such that
            // we take all elements > T and some elements == T.
            let mut low: i64 = 0;
            let mut high: i64 = max_val;
            let mut row_thresh: i64 = 0;
            let mut found: bool = false;

            while low <= high {
                let mid = (low + high) / 2;
                let mut cnt_gt: i64 = 0;
                let mut cnt_eq: i64 = 0;
                let mut j2 = 0;
                while j2 < m {
                    let v = row[j2];
                    if v > mid {
                        cnt_gt += 1;
                    } else if v == mid {
                        cnt_eq += 1;
                    }
                    j2 += 1;
                }

                if cnt_gt >= lim {
                    low = mid + 1;
                } else if cnt_gt + cnt_eq >= lim {
                    row_thresh = mid;
                    found = true;
                    break;
                } else {
                    high = mid - 1;
                }
            }

            if found {
                // Push all elements strictly greater than the threshold.
                let mut cnt_gt: i64 = 0;
                let mut j3 = 0;
                while j3 < m {
                    let v = row[j3];
                    if v > row_thresh {
                        candidates.push(v);
                        cnt_gt += 1;
                    }
                    j3 += 1;
                }

                // Push enough copies of the threshold to reach the limit.
                let mut needed = lim - cnt_gt;
                while needed > 0 {
                    candidates.push(row_thresh);
                    needed -= 1;
                }
            }
        }

        i += 1;
    }

    if k <= 0 || candidates.len() == 0 {
        return 0;
    }

    // Find the maximum candidate value.
    let mut max_cand: i64 = 0;
    let mut idx = 0;
    while idx < candidates.len() {
        if candidates[idx] > max_cand {
            max_cand = candidates[idx];
        }
        idx += 1;
    }

    // Binary search for the global threshold.
    let mut low: i64 = 0;
    let mut high: i64 = max_cand;
    let mut thresh: i64 = 0;
    let mut found: bool = false;

    while low <= high {
        let mid = (low + high) / 2;
        let mut cnt_gt: i64 = 0;
        let mut cnt_eq: i64 = 0;
        let mut idx2 = 0;
        while idx2 < candidates.len() {
            let v = candidates[idx2];
            if v > mid {
                cnt_gt += 1;
            } else if v == mid {
                cnt_eq += 1;
            }
            idx2 += 1;
        }

        if cnt_gt >= k {
            low = mid + 1;
        } else if cnt_gt + cnt_eq >= k {
            thresh = mid;
            found = true;
            break;
        } else {
            high = mid - 1;
        }
    }

    let mut ans: i64 = 0;
    if found {
        let mut sum_gt: i64 = 0;
        let mut cnt_gt: i64 = 0;
        let mut idx3 = 0;
        while idx3 < candidates.len() {
            let v = candidates[idx3];
            if v > thresh {
                sum_gt += v;
                cnt_gt += 1;
            }
            idx3 += 1;
        }
        ans = sum_gt + (k - cnt_gt) * thresh;
    } else {
        // k exceeds the total number of candidates: sum all of them.
        let mut idx4 = 0;
        while idx4 < candidates.len() {
            ans += candidates[idx4];
            idx4 += 1;
        }
    }

    ans
}
