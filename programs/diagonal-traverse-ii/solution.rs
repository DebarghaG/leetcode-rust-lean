pub fn find_diagonal_order(nums: &[Vec<i64>]) -> Vec<i64> {
    let r = nums.len();
    if r == 0 {
        return Vec::new();
    }

    let mut max_sum: usize = 0;
    let mut i: usize = 0;
    while i < r {
        let len = nums[i].len();
        if len > 0 {
            let s = i + len - 1;
            if s > max_sum {
                max_sum = s;
            }
        }
        i += 1;
    }

    let bucket_count = max_sum + 1;
    let mut buckets: Vec<Vec<i64>> = Vec::new();
    let mut b: usize = 0;
    while b < bucket_count {
        buckets.push(Vec::new());
        b += 1;
    }

    let mut ri: usize = r;
    while ri > 0 {
        ri -= 1;
        let row = &nums[ri];
        let mut j: usize = 0;
        while j < row.len() {
            let d = ri + j;
            let value = row[j];
            buckets[d].push(value);
            j += 1;
        }
    }

    let mut out: Vec<i64> = Vec::new();
    let mut d: usize = 0;
    while d < bucket_count {
        let bucket = &buckets[d];
        let mut k: usize = 0;
        while k < bucket.len() {
            out.push(bucket[k]);
            k += 1;
        }
        d += 1;
    }

    out
}
