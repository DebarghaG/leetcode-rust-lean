pub fn min_or_after_operations(nums: &[i64], k: i64) -> i64 {
    let n: i64 = nums.len() as i64;
    let need: i64 = n - k;

    let mut forbidden: i64 = 0;
    let mut answer: i64 = 0;

    let mut bit: i64 = 1 << 29;

    while bit > 0 {
        let test_mask: i64 = forbidden | bit;

        let mut cur: i64 = test_mask;
        let mut groups: i64 = 0;
        let mut i: usize = 0;

        while i < nums.len() {
            cur &= nums[i];

            if (cur & test_mask) == 0 {
                groups += 1;
                cur = test_mask;
            }

            i += 1;
        }

        if groups >= need {
            forbidden = test_mask;
        } else {
            answer |= bit;
        }

        bit >>= 1;
    }

    answer
}
