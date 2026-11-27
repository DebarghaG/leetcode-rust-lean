fn find_index(vals: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = vals.len();

    while lo < hi {
        let mid: usize = lo + (hi - lo) / 2;

        if vals[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}

pub fn max_sum(nums: &[i64], m: i64, k: i64) -> i64 {
    let n: usize = nums.len();
    let kk: usize = k as usize;

    if kk == 0 || kk > n {
        return 0;
    }

    let mut vals: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        vals.push(nums[i]);
        i += 1;
    }

    vals.sort();

    let mut uniq: Vec<i64> = Vec::new();
    i = 0;

    while i < vals.len() {
        if i == 0 || vals[i] != vals[i - 1] {
            uniq.push(vals[i]);
        }
        i += 1;
    }

    let mut freq: Vec<i64> = Vec::new();
    i = 0;

    while i < uniq.len() {
        freq.push(0);
        i += 1;
    }

    let mut distinct: i64 = 0;
    let mut sum: i64 = 0;

    i = 0;
    while i < kk {
        let id: usize = find_index(&uniq, nums[i]);

        if freq[id] == 0 {
            distinct += 1;
        }

        freq[id] += 1;
        sum += nums[i];
        i += 1;
    }

    let mut ans: i64 = 0;

    if distinct >= m {
        ans = sum;
    }

    let mut start: usize = 0;

    while start + kk < n {
        let out_id: usize = find_index(&uniq, nums[start]);

        freq[out_id] -= 1;
        if freq[out_id] == 0 {
            distinct -= 1;
        }

        sum -= nums[start];

        let in_idx: usize = start + kk;
        let in_id: usize = find_index(&uniq, nums[in_idx]);

        if freq[in_id] == 0 {
            distinct += 1;
        }

        freq[in_id] += 1;
        sum += nums[in_idx];

        if distinct >= m && sum > ans {
            ans = sum;
        }

        start += 1;
    }

    ans
}
