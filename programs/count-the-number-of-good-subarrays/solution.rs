pub fn count_good(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    if k <= 0 {
        let n64 = n as i64;
        return n64 * (n64 + 1) / 2;
    }

    if n == 0 {
        return 0;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }
    sorted.sort();

    let mut uniq: Vec<i64> = Vec::new();
    i = 0;
    while i < sorted.len() {
        if i == 0 || sorted[i] != sorted[i - 1] {
            uniq.push(sorted[i]);
        }
        i += 1;
    }

    let m = uniq.len();
    let mut freq: Vec<i64> = Vec::new();
    i = 0;
    while i < m {
        freq.push(0);
        i += 1;
    }

    let mut ans: i64 = 0;
    let mut pairs: i64 = 0;
    let mut left: usize = 0;
    let mut right: usize = 0;

    while right < n {
        let x = nums[right];
        let idx = find_index(&uniq, x);
        let c = freq[idx];
        pairs += c;
        freq[idx] = c + 1;
        right += 1;

        while pairs >= k {
            let y = nums[left];
            let idx2 = find_index(&uniq, y);
            let c2 = freq[idx2];
            freq[idx2] = c2 - 1;
            pairs -= c2 - 1;
            left += 1;
        }

        ans += left as i64;
    }

    ans
}

fn find_index(uniq: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = uniq.len();

    while lo < hi {
        let mid = (lo + hi) / 2;
        if uniq[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    lo
}
