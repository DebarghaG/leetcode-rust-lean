// Count how many present values are "better" (rank higher) than value index v.
// A value u is better than v if freq[u] > freq[v], or freq[u] == freq[v] and u > v.
fn count_better(counts: &[i64], v: usize) -> i64 {
    let m = counts.len();
    let fv = counts[v];
    let mut cnt: i64 = 0;
    let mut u: usize = 0;
    while u < m {
        let fu = counts[u];
        if fu > 0 {
            if u != v {
                let mut is_better = false;
                if fu > fv {
                    is_better = true;
                } else if fu == fv {
                    if u > v {
                        is_better = true;
                    }
                }
                if is_better {
                    cnt = cnt + 1;
                }
            }
        }
        u = u + 1;
    }
    cnt
}

// Sum of the occurrences of the top-x most frequent distinct values.
fn xsum(counts: &[i64], x: i64) -> i64 {
    let m = counts.len();
    let mut sum: i64 = 0;
    let mut v: usize = 0;
    while v < m {
        let fv = counts[v];
        if fv > 0 {
            let r = count_better(counts, v);
            if r < x {
                sum = sum + fv * (v as i64);
            }
        }
        v = v + 1;
    }
    sum
}

pub fn find_x_sum(nums: &[i64], k: i64, x: i64) -> Vec<i64> {
    let n = nums.len();
    let mut ans: Vec<i64> = Vec::new();
    if n == 0 {
        return ans;
    }
    if k <= 0 {
        return ans;
    }
    let kk = k as usize;
    if kk > n {
        return ans;
    }

    // Determine the value range so counts has enough slots.
    let mut max_val: i64 = 1;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i = i + 1;
    }
    let count_len = (max_val as usize) + 1;

    let mut counts: Vec<i64> = Vec::new();
    let mut c: usize = 0;
    while c < count_len {
        counts.push(0);
        c = c + 1;
    }

    // Initial counts for the first window.
    let mut j: usize = 0;
    while j < kk {
        let idx = nums[j] as usize;
        counts[idx] = counts[idx] + 1;
        j = j + 1;
    }

    let windows = n - kk + 1;
    let mut start: usize = 0;
    while start < windows {
        let s = xsum(&counts, x);
        ans.push(s);

        // Slide the window: drop nums[start], add nums[start + kk].
        if start + 1 < windows {
            let o = nums[start] as usize;
            counts[o] = counts[o] - 1;
            let ni = nums[start + kk] as usize;
            counts[ni] = counts[ni] + 1;
        }

        start = start + 1;
    }

    ans
}
