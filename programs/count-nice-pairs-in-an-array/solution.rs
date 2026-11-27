fn reverse_num(mut x: i64) -> i64 {
    let mut r: i64 = 0;
    while x > 0 {
        r = r * 10 + (x % 10);
        x = x / 10;
    }
    r
}

fn merge_sort(mut a: Vec<i64>) -> Vec<i64> {
    let n = a.len();
    let mut width: usize = 1;

    while width < n {
        let mut merged: Vec<i64> = Vec::new();
        let mut left: usize = 0;

        while left < n {
            let mid = if left + width < n {
                left + width
            } else {
                n
            };

            let right = if left + 2 * width < n {
                left + 2 * width
            } else {
                n
            };

            let mut i: usize = left;
            let mut j: usize = mid;

            while i < mid && j < right {
                if a[i] <= a[j] {
                    merged.push(a[i]);
                    i += 1;
                } else {
                    merged.push(a[j]);
                    j += 1;
                }
            }

            while i < mid {
                merged.push(a[i]);
                i += 1;
            }

            while j < right {
                merged.push(a[j]);
                j += 1;
            }

            left = right;
        }

        a = merged;
        width = width * 2;
    }

    a
}

pub fn count_nice_pairs(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut diffs: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n {
        let x = nums[i];
        let r = reverse_num(x);
        diffs.push(x - r);
        i += 1;
    }

    let sorted = merge_sort(diffs);

    let modulo: i64 = 1000000007;
    let mut ans: i64 = 0;
    let m = sorted.len();
    let mut p: usize = 0;

    while p < m {
        let value = sorted[p];
        let mut count: i64 = 0;

        while p < m && sorted[p] == value {
            count += 1;
            p += 1;
        }

        let pairs = count * (count - 1) / 2;
        ans = (ans + pairs % modulo) % modulo;
    }

    ans
}
