pub fn length_of_lis(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut max_v: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] > max_v {
            max_v = nums[i];
        }
        i += 1;
    }

    let target: usize = (max_v as usize) + 1;
    let mut size: usize = 1;
    while size < target {
        size *= 2;
    }

    let mut tree: Vec<i64> = Vec::new();
    let total = size * 2;
    let mut j: usize = 0;
    while j < total {
        tree.push(0);
        j += 1;
    }

    let mut ans: i64 = 0;
    i = 0;
    while i < n {
        let x = nums[i];

        let mut best: i64 = 0;
        if x > 1 {
            let mut low = x - k;
            if low < 1 {
                low = 1;
            }
            let high = x;

            if low < high {
                let mut l = (low as usize) + size;
                let mut r = (high as usize) + size;

                while l < r {
                    if l % 2 == 1 {
                        if tree[l] > best {
                            best = tree[l];
                        }
                        l += 1;
                    }
                    if r % 2 == 1 {
                        r -= 1;
                        if tree[r] > best {
                            best = tree[r];
                        }
                    }
                    l /= 2;
                    r /= 2;
                }
            }
        }

        let cur = best + 1;

        let pos = x as usize;
        let mut idx = size + pos;
        if cur > tree[idx] {
            tree[idx] = cur;
        }

        idx /= 2;
        while idx > 0 {
            let left = tree[2 * idx];
            let right = tree[2 * idx + 1];
            let mut m = left;
            if right > m {
                m = right;
            }
            tree[idx] = m;
            idx /= 2;
        }

        if cur > ans {
            ans = cur;
        }

        i += 1;
    }

    ans
}
