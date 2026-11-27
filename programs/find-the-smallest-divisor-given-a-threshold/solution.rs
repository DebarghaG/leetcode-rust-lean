pub fn smallest_divisor(nums: &[i64], threshold: i64) -> i64 {
    let n = nums.len();

    // Find the maximum element.
    let mut maxv: i64 = 1;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > maxv {
            maxv = nums[i];
        }
        i += 1;
    }

    // Use an exclusive upper bound maxv + 1. When n <= threshold this is
    // feasible (every element contributes 1), and the true answer is <= maxv,
    // so the binary search still finds the minimal feasible divisor. For the
    // degenerate case (n > threshold) this also matches the usual reference
    // which searches up to max + 1.
    let mut hi: i64 = maxv + 1;
    let mut lo: i64 = 1;

    while lo < hi {
        let mid: i64 = lo + (hi - lo) / 2;
        if feasible(nums, mid, threshold) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

// Returns true iff sum(ceil(nums[i] / d)) <= threshold.
// The running total never exceeds threshold (early exit), so it cannot
// overflow, and ceil is computed without any overflow-prone addition.
fn feasible(nums: &[i64], d: i64, threshold: i64) -> bool {
    let n = nums.len();
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];
        let q = x / d;
        let r = x % d;
        let mut term = q;
        if r != 0 {
            term = q + 1;
        }

        // total <= threshold is invariant; threshold - total is safe.
        if term > threshold - total {
            return false;
        }
        total += term;
        i += 1;
    }

    true
}
