fn find_index(vals: &[i64], target: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = vals.len();

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;
        if vals[mid] < target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    if lo < vals.len() && vals[lo] == target {
        lo
    } else {
        vals.len()
    }
}

pub fn maximum_length(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n == 0 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }
    sorted.sort();

    let mut vals: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < n {
        let v: i64 = sorted[j];
        let mut c: i64 = 0;
        while j < n && sorted[j] == v {
            c += 1;
            j += 1;
        }
        vals.push(v);
        counts.push(c);
    }

    let mut ans: i64 = 1;

    let idx1: usize = find_index(&vals, 1);
    if idx1 < vals.len() {
        let c: i64 = counts[idx1];
        let mut odd: i64 = c;
        if c % 2 == 0 {
            odd = c - 1;
        }
        if odd > ans {
            ans = odd;
        }
    }

    let m: usize = vals.len();
    let mut idx: usize = 0;

    while idx < m {
        let x: i64 = vals[idx];

        if x != 1 {
            let mut cur: i64 = x;
            let mut cur_count: i64 = counts[idx];
            let mut depth: i64 = 0;

            while cur_count >= 2 {
                if cur > 3_037_000_499 {
                    break;
                }

                let next: i64 = cur * cur;
                let ni: usize = find_index(&vals, next);

                if ni == m {
                    break;
                }

                cur = next;
                cur_count = counts[ni];
                depth += 1;
            }

            let len: i64 = depth * 2 + 1;
            if len > ans {
                ans = len;
            }
        }

        idx += 1;
    }

    ans
}
