fn subset_sums(nums: &[i64], start: usize, end: usize) -> Vec<i64> {
    let mut sums: Vec<i64> = Vec::new();
    sums.push(0);

    let mut i = start;
    while i < end {
        let x = nums[i];
        let old_len = sums.len();
        let mut j = 0usize;
        while j < old_len {
            let s = sums[j];
            sums.push(s + x);
            j += 1;
        }
        i += 1;
    }

    sums
}

fn sort_vec(mut v: Vec<i64>) -> Vec<i64> {
    let n = v.len();
    if n <= 1 {
        return v;
    }

    let mut tmp: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n {
        tmp.push(0);
        i += 1;
    }

    let mut width = 1usize;
    while width < n {
        let mut left = 0usize;
        while left < n {
            let mid = if left + width < n { left + width } else { n };
            let right = if left + 2usize * width < n {
                left + 2usize * width
            } else {
                n
            };

            let mut a = left;
            let mut b = mid;
            let mut k = left;

            while a < mid && b < right {
                if v[a] <= v[b] {
                    tmp[k] = v[a];
                    a += 1;
                } else {
                    tmp[k] = v[b];
                    b += 1;
                }
                k += 1;
            }

            while a < mid {
                tmp[k] = v[a];
                a += 1;
                k += 1;
            }

            while b < right {
                tmp[k] = v[b];
                b += 1;
                k += 1;
            }

            left = left + 2usize * width;
        }

        let mut p = 0usize;
        while p < n {
            v[p] = tmp[p];
            p += 1;
        }

        width = width * 2usize;
    }

    v
}

pub fn min_abs_difference(nums: &[i64], goal: i64) -> i64 {
    let n = nums.len();
    let mid = n / 2;

    let left_sums = subset_sums(nums, 0, mid);
    let right_sums = subset_sums(nums, mid, n);

    let left_sums = sort_vec(left_sums);
    let right_sums = sort_vec(right_sums);

    let left_len = left_sums.len();
    let right_len = right_sums.len();

    let mut best: i64 = 1000000000000000000;

    let mut i = 0usize;
    let mut j = right_len;

    while i < left_len && j > 0 {
        let sum = left_sums[i] + right_sums[j - 1];
        let mut diff = sum - goal;
        if diff < 0 {
            diff = -diff;
        }

        if diff < best {
            best = diff;
        }
        if best == 0 {
            return 0;
        }

        if sum > goal {
            j -= 1;
        } else {
            i += 1;
        }
    }

    best
}
