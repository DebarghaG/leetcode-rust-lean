pub fn maximum_product(nums: &[i64]) -> i64 {
    let mut max1: i64 = -1000000;
    let mut max2: i64 = -1000000;
    let mut max3: i64 = -1000000;

    let mut min1: i64 = 1000000;
    let mut min2: i64 = 1000000;

    let n: usize = nums.len();
    let mut i: usize = 0;

    while i < n {
        let x: i64 = nums[i];

        if x > max1 {
            max3 = max2;
            max2 = max1;
            max1 = x;
        } else if x > max2 {
            max3 = max2;
            max2 = x;
        } else if x > max3 {
            max3 = x;
        }

        if x < min1 {
            min2 = min1;
            min1 = x;
        } else if x < min2 {
            min2 = x;
        }

        i = i + 1;
    }

    let product_largest_three: i64 = max1 * max2 * max3;
    let product_two_smallest_and_largest: i64 = min1 * min2 * max1;

    if product_largest_three > product_two_smallest_and_largest {
        product_largest_three
    } else {
        product_two_smallest_and_largest
    }
}
