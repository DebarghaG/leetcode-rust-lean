fn abs_i64(x: i64) -> i64 {
    if x < 0 {
        -x
    } else {
        x
    }
}

fn build_groups(nums: &[i64], start: usize, end: usize) -> Vec<Vec<i64>> {
    let h = end - start;

    let mut groups: Vec<Vec<i64>> = Vec::new();
    let mut i: usize = 0;
    while i <= h {
        groups.push(Vec::new());
        i += 1;
    }

    let mut total_masks: usize = 1;
    let mut t: usize = 0;
    while t < h {
        total_masks *= 2;
        t += 1;
    }

    let mut mask: usize = 0;
    while mask < total_masks {
        let mut sum: i64 = 0;
        let mut cnt: usize = 0;

        let mut j: usize = 0;
        while j < h {
            if ((mask >> j) & 1usize) == 1usize {
                sum += nums[start + j];
                cnt += 1;
            }
            j += 1;
        }

        groups[cnt].push(sum);
        mask += 1;
    }

    let mut g: usize = 0;
    while g < groups.len() {
        groups[g].sort();
        g += 1;
    }

    groups
}

pub fn minimum_difference(nums: &[i64]) -> i64 {
    let len = nums.len();
    let n = len / 2;
    let mid = n;

    let left = build_groups(nums, 0, mid);
    let right = build_groups(nums, mid, len);

    let mut total: i64 = 0;
    let mut i: usize = 0;
    while i < len {
        total += nums[i];
        i += 1;
    }

    let mut best: i64 = 1000000000000000000i64;

    let mut ka: usize = 0;
    while ka <= n {
        let kb = n - ka;

        if ka < left.len() && kb < right.len() {
            let a_list = &left[ka];
            let b_list = &right[kb];

            let mut ai: usize = 0;
            while ai < a_list.len() {
                let a = a_list[ai];

                let mut lo: usize = 0;
                let mut hi: usize = b_list.len();

                while lo < hi {
                    let m = (lo + hi) / 2;
                    let value = 2i64 * (a + b_list[m]);

                    if value < total {
                        lo = m + 1;
                    } else {
                        hi = m;
                    }
                }

                if lo < b_list.len() {
                    let diff = abs_i64(total - 2i64 * (a + b_list[lo]));
                    if diff < best {
                        best = diff;
                    }
                }

                if lo > 0 {
                    let diff = abs_i64(total - 2i64 * (a + b_list[lo - 1]));
                    if diff < best {
                        best = diff;
                    }
                }

                ai += 1;
            }
        }

        ka += 1;
    }

    best
}
