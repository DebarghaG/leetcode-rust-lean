pub fn min_moves2(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    v.sort();

    let mid = n / 2;
    let median = v[mid];

    let mut total: i64 = 0;
    let mut j: usize = 0;
    while j < n {
        let x = v[j];
        if x < median {
            total += median - x;
        } else {
            total += x - median;
        }
        j += 1;
    }

    total
}
