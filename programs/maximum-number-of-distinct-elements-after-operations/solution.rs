pub fn max_distinct_elements(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    v.sort();

    let mut ans: i64 = 0;
    let mut prev: i64 = 0;
    let mut have_prev: bool = false;
    let mut j: usize = 0;

    while j < n {
        let x = v[j];
        let low = x - k;
        let high = x + k;

        if !have_prev {
            ans += 1;
            prev = low;
            have_prev = true;
        } else {
            let mut candidate = prev + 1;
            if low > candidate {
                candidate = low;
            }

            if candidate <= high {
                ans += 1;
                prev = candidate;
            }
        }

        j += 1;
    }

    ans
}
