pub fn lexicographically_smallest_array(nums: &[i64], limit: i64) -> Vec<i64> {
    let n: usize = nums.len();
    let mut ans: Vec<i64> = Vec::new();

    if n == 0 {
        return ans;
    }

    let base: i64 = (n as i64) + 1;

    let mut keys: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        let key: i64 = nums[i] * base + (i as i64);
        keys.push(key);
        i += 1;
    }
    keys.sort();

    i = 0;
    while i < n {
        ans.push(0);
        i += 1;
    }

    let mut start: usize = 0;
    while start < n {
        let mut end: usize = start;

        while end + 1 < n {
            let v1: i64 = keys[end] / base;
            let v2: i64 = keys[end + 1] / base;
            if v2 - v1 <= limit {
                end += 1;
            } else {
                break;
            }
        }

        let mut positions: Vec<i64> = Vec::new();
        let mut j: usize = start;
        while j <= end {
            positions.push(keys[j] % base);
            j += 1;
        }
        positions.sort();

        let mut k: usize = 0;
        while k < positions.len() {
            let value: i64 = keys[start + k] / base;
            let pos: usize = positions[k] as usize;
            ans[pos] = value;
            k += 1;
        }

        start = end + 1;
    }

    ans
}
