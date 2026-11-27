pub fn trap(height: &[i64]) -> i64 {
    let n = height.len();
    if n == 0 {
        return 0;
    }

    let mut left: usize = 0;
    let mut right: usize = n - 1;
    let mut left_max: i64 = 0;
    let mut right_max: i64 = 0;
    let mut water: i64 = 0;

    while left < right {
        if height[left] < height[right] {
            if height[left] >= left_max {
                left_max = height[left];
            } else {
                water += left_max - height[left];
            }
            left += 1;
        } else {
            if height[right] >= right_max {
                right_max = height[right];
            } else {
                water += right_max - height[right];
            }
            right -= 1;
        }
    }

    water
}
