pub fn majority_element(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();

    let mut candidate1: i64 = 0;
    let mut candidate2: i64 = 1;
    let mut count1: i64 = 0;
    let mut count2: i64 = 0;

    let mut i: usize = 0;
    while i < n {
        let num = nums[i];

        if num == candidate1 {
            count1 += 1;
        } else if num == candidate2 {
            count2 += 1;
        } else if count1 == 0 {
            candidate1 = num;
            count1 = 1;
        } else if count2 == 0 {
            candidate2 = num;
            count2 = 1;
        } else {
            count1 -= 1;
            count2 -= 1;
        }

        i += 1;
    }

    let mut real1: i64 = 0;
    let mut real2: i64 = 0;

    i = 0;
    while i < n {
        let num = nums[i];

        if num == candidate1 {
            real1 += 1;
        } else if num == candidate2 {
            real2 += 1;
        }

        i += 1;
    }

    let threshold: i64 = (n / 3) as i64;
    let mut result: Vec<i64> = Vec::new();

    if real1 > threshold {
        result.push(candidate1);
    }
    if real2 > threshold {
        result.push(candidate2);
    }

    result
}
