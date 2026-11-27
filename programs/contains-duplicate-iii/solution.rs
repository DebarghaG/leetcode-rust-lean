fn lower_bound(v: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] < x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn upper_bound(v: &[i64], x: i64) -> usize {
    let mut lo: usize = 0;
    let mut hi: usize = v.len();
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if v[mid] <= x {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    lo
}

fn bit_add(bit: &mut Vec<i64>, n: usize, idx: usize, delta: i64) {
    let mut i = idx + 1;
    while i <= n {
        bit[i] = bit[i] + delta;
        i = i + (i - (i & (i - 1)));
    }
}

fn bit_sum(bit: &[i64], mut i: usize) -> i64 {
    let mut s: i64 = 0;
    while i > 0 {
        s = s + bit[i];
        i = i & (i - 1);
    }
    s
}

fn manual_sort(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut z: usize = 0;
    while z < n {
        temp.push(0);
        z += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut left: usize = 0;
        while left < n {
            let mut mid = left + width;
            if mid > n {
                mid = n;
            }

            let mut right = mid + width;
            if right > n {
                right = n;
            }

            let mut i = left;
            let mut j = mid;
            let mut k = left;

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

        let mut t: usize = 0;
        while t < n {
            v[t] = temp[t];
            t += 1;
        }

        width = width * 2;
    }
}

pub fn contains_nearby_almost_duplicate(nums: &[i64], indexDiff: i64, valueDiff: i64) -> bool {
    let n = nums.len();

    if n < 2 {
        return false;
    }
    if indexDiff <= 0 {
        return false;
    }
    if valueDiff < 0 {
        return false;
    }

    let mut sorted: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        sorted.push(nums[i]);
        i += 1;
    }
    manual_sort(&mut sorted);

    let mut bit: Vec<i64> = Vec::new();
    let mut j: usize = 0;
    while j <= n {
        bit.push(0);
        j += 1;
    }

    i = 0;
    while i < n {
        let low = nums[i] - valueDiff;
        let high = nums[i] + valueDiff;

        let l = lower_bound(&sorted, low);
        let r = upper_bound(&sorted, high);

        if l < r {
            let cnt = bit_sum(&bit, r) - bit_sum(&bit, l);
            if cnt > 0 {
                return true;
            }
        }

        let pos = lower_bound(&sorted, nums[i]);
        bit_add(&mut bit, n, pos, 1);

        if (i as i64) >= indexDiff {
            let rem_i = i - (indexDiff as usize);
            let rem_pos = lower_bound(&sorted, nums[rem_i]);
            bit_add(&mut bit, n, rem_pos, -1);
        }

        i += 1;
    }

    false
}
