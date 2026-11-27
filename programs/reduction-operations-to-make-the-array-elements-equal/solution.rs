pub fn reduction_operations(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut max_val = nums[0];
    let mut i: usize = 1;
    while i < n {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i += 1;
    }

    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n {
        b.push(0);
        i += 1;
    }

    let mut count: Vec<i64> = Vec::new();
    let mut d: usize = 0;
    while d < 256 {
        count.push(0);
        d += 1;
    }

    let mut exp: i64 = 1;
    let mut sorting: bool = max_val > 0;
    while sorting {
        let mut d: usize = 0;
        while d < 256 {
            count[d] = 0;
            d += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let digit_i64 = (a[i] / exp) % 256;
            let digit = digit_i64 as usize;
            count[digit] = count[digit] + 1;
            i += 1;
        }

        let mut sum: i64 = 0;
        let mut d: usize = 0;
        while d < 256 {
            let c = count[d];
            count[d] = sum;
            sum = sum + c;
            d += 1;
        }

        let mut i: usize = 0;
        while i < n {
            let digit_i64 = (a[i] / exp) % 256;
            let digit = digit_i64 as usize;
            let pos_i64 = count[digit];
            let pos = pos_i64 as usize;
            b[pos] = a[i];
            count[digit] = pos_i64 + 1;
            i += 1;
        }

        let mut i: usize = 0;
        while i < n {
            a[i] = b[i];
            i += 1;
        }

        if exp > max_val / 256 {
            sorting = false;
        } else {
            exp = exp * 256;
        }
    }

    let mut ans: i64 = 0;
    let mut distinct_less: i64 = 0;
    let mut i: usize = 1;
    while i < n {
        if a[i] != a[i - 1] {
            distinct_less = distinct_less + 1;
        }
        ans = ans + distinct_less;
        i += 1;
    }

    ans
}
