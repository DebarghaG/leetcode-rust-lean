pub fn is_possible(nums: &[i64]) -> bool {
    let n: usize = nums.len();
    if n < 3 {
        return false;
    }

    let size: usize = 2005;

    let mut freq: Vec<i64> = Vec::new();
    let mut need: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < size {
        freq.push(0);
        need.push(0);
        i += 1;
    }

    let mut idx: usize = 0;
    while idx < n {
        let v: i64 = nums[idx];
        let q: usize = (v + 1000) as usize;
        freq[q] = freq[q] + 1;
        idx += 1;
    }

    let mut ok: bool = true;
    let mut p: usize = 0;

    while p < 2001 {
        while freq[p] > 0 && ok {
            if need[p] > 0 {
                need[p] = need[p] - 1;
                need[p + 1] = need[p + 1] + 1;
                freq[p] = freq[p] - 1;
            } else if freq[p + 1] > 0 && freq[p + 2] > 0 {
                freq[p] = freq[p] - 1;
                freq[p + 1] = freq[p + 1] - 1;
                freq[p + 2] = freq[p + 2] - 1;
                need[p + 3] = need[p + 3] + 1;
            } else {
                ok = false;
            }
        }
        p += 1;
    }

    ok
}
