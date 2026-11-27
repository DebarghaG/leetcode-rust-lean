pub fn max_product_difference(nums: &[i64]) -> i64 {
    let mut max1 = nums[0];
    let mut max2 = nums[1];

    if max2 > max1 {
        let tmp = max1;
        max1 = max2;
        max2 = tmp;
    }

    let mut min1 = nums[0];
    let mut min2 = nums[1];

    if min2 < min1 {
        let tmp = min1;
        min1 = min2;
        min2 = tmp;
    }

    let n = nums.len();
    let mut i = 2;

    while i < n {
        let v = nums[i];

        if v > max1 {
            max2 = max1;
            max1 = v;
        } else if v > max2 {
            max2 = v;
        }

        if v < min1 {
            min2 = min1;
            min1 = v;
        } else if v < min2 {
            min2 = v;
        }

        i = i + 1;
    }

    max1 * max2 - min1 * min2
}
