pub fn sum_four_divisors(nums: &[i64]) -> i64 {
    let mut total: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        let n: i64 = nums[i];

        let mut count: i64 = 0;
        let mut sum: i64 = 0;
        let mut d: i64 = 1;

        while d * d <= n {
            if n % d == 0 {
                let q: i64 = n / d;

                count += 1;
                sum += d;

                if q != d {
                    count += 1;
                    sum += q;
                }
            }

            d += 1;
        }

        if count == 4 {
            total += sum;
        }

        i += 1;
    }

    total
}
