pub fn distinct_averages(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut v: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n {
        v.push(nums[idx]);
        idx += 1;
    }

    // Selection sort the copied array.
    let mut i: usize = 0;
    while i < n {
        let mut min_i: usize = i;
        let mut j: usize = i + 1;
        while j < n {
            if v[j] < v[min_i] {
                min_i = j;
            }
            j += 1;
        }

        if min_i != i {
            let tmp = v[i];
            v[i] = v[min_i];
            v[min_i] = tmp;
        }

        i += 1;
    }

    // Pair the smallest with the largest, the second-smallest with the
    // second-largest, etc. Count distinct pair sums, which are equivalent
    // to distinct averages.
    let mut seen: Vec<i64> = Vec::new();
    let half = n / 2;
    let mut k: usize = 0;

    while k < half {
        let sum = v[k] + v[n - 1 - k];

        let mut found = false;
        let mut t: usize = 0;
        while t < seen.len() {
            if seen[t] == sum {
                found = true;
            }
            t += 1;
        }

        if !found {
            seen.push(sum);
        }

        k += 1;
    }

    seen.len() as i64
}
