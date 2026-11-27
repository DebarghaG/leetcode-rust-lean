pub fn min_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut tails: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];

        // Find the first position where tails[pos] < x.
        // tails is maintained in non-increasing order.
        let mut lo: usize = 0;
        let mut hi: usize = tails.len();

        while lo < hi {
            let mid: usize = lo + (hi - lo) / 2;
            if tails[mid] < x {
                hi = mid;
            } else {
                lo = mid + 1;
            }
        }

        if lo < tails.len() {
            tails[lo] = x;
        } else {
            tails.push(x);
        }

        i += 1;
    }

    tails.len() as i64
}
