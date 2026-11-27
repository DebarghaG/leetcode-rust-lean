const MOD: i64 = 1_000_000_007;

fn sorted_copy(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        v.push(nums[i]);
        i += 1;
    }

    if n <= 1 {
        return v;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < n {
        temp.push(0);
        t += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mid = if left + width < n {
                left + width
            } else {
                n
            };
            let right = if left + width * 2 < n {
                left + width * 2
            } else {
                n
            };

            let mut i: usize = left;
            let mut j: usize = mid;
            let mut k: usize = left;

            while i < mid && j < right {
                if v[i] <= v[j] {
                    temp[k] = v[i];
                    i += 1;
                } else {
                    temp[k] = v[j];
                    j += 1;
                }
                k += 1;
            }

            while i < mid {
                temp[k] = v[i];
                i += 1;
                k += 1;
            }

            while j < right {
                temp[k] = v[j];
                j += 1;
                k += 1;
            }

            left = right;
        }

        let mut p: usize = 0;
        while p < n {
            v[p] = temp[p];
            p += 1;
        }

        width = width * 2;
    }

    v
}

pub fn min_absolute_sum_diff(nums1: &[i64], nums2: &[i64]) -> i64 {
    let n = nums1.len();
    let sorted = sorted_copy(nums1);

    let mut total: i64 = 0;
    let mut max_gain: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let a = nums1[i];
        let b = nums2[i];

        let mut cur = a - b;
        if cur < 0 {
            cur = -cur;
        }
        total += cur;

        let mut lo: usize = 0;
        let mut hi: usize = sorted.len();
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if sorted[mid] < b {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        let pos = lo;

        let mut best = cur;

        if pos < sorted.len() {
            let mut d = sorted[pos] - b;
            if d < 0 {
                d = -d;
            }
            if d < best {
                best = d;
            }
        }

        if pos > 0 {
            let mut d = sorted[pos - 1] - b;
            if d < 0 {
                d = -d;
            }
            if d < best {
                best = d;
            }
        }

        let gain = cur - best;
        if gain > max_gain {
            max_gain = gain;
        }

        i += 1;
    }

    let answer = total - max_gain;
    answer % MOD
}
