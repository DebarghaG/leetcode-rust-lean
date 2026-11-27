const MOD: i64 = 1_000_000_007;

fn sort_i64(v: &mut Vec<i64>) {
    let n = v.len();
    if n <= 1 {
        return;
    }

    let mut temp: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        temp.push(0);
        i += 1;
    }

    let mut width: usize = 1;
    while width < n {
        let mut start: usize = 0;

        while start < n {
            let mid = if start + width < n {
                start + width
            } else {
                n
            };

            let end = if start + 2 * width < n {
                start + 2 * width
            } else {
                n
            };

            let mut left = start;
            let mut right = mid;
            let mut out = start;

            while left < mid && right < end {
                if v[left] <= v[right] {
                    temp[out] = v[left];
                    left += 1;
                } else {
                    temp[out] = v[right];
                    right += 1;
                }
                out += 1;
            }

            while left < mid {
                temp[out] = v[left];
                left += 1;
                out += 1;
            }

            while right < end {
                temp[out] = v[right];
                right += 1;
                out += 1;
            }

            start = end;
        }

        let mut c = 0;
        while c < n {
            v[c] = temp[c];
            c += 1;
        }

        width *= 2;
    }
}

pub fn sum_of_power(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    sort_i64(&mut a);

    let mut ans: i64 = 0;
    let mut prefix: i64 = 0;

    let mut idx = 0;
    while idx < n {
        let x = a[idx] % MOD;
        let square = (x * x) % MOD;
        let inner = (prefix + x) % MOD;
        let term = (square * inner) % MOD;

        ans = (ans + term) % MOD;
        prefix = (prefix * 2 + x) % MOD;

        idx += 1;
    }

    ans
}
