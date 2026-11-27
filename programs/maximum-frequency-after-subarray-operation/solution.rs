pub fn max_frequency(nums: &[i64], k: i64) -> i64 {
    let n = nums.len();

    let mut total_k: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] == k {
            total_k += 1;
        }
        i += 1;
    }

    let mut best_gain: i64 = 0;
    let mut c: i64 = 1;

    while c <= 50 {
        if c != k {
            let mut current: i64 = 0;
            let mut best_for_c: i64 = 0;
            let mut j: usize = 0;

            while j < n {
                let value = nums[j];

                if value == c {
                    current += 1;
                } else if value == k {
                    current -= 1;
                }

                if current > best_for_c {
                    best_for_c = current;
                }
                if current < 0 {
                    current = 0;
                }

                j += 1;
            }

            if best_for_c > best_gain {
                best_gain = best_for_c;
            }
        }

        c += 1;
    }

    total_k + best_gain
}
