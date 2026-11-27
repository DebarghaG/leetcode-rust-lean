pub fn special_array(nums: &[i64]) -> i64 {
    let n: i64 = nums.len() as i64;
    let mut x: i64 = 0;

    while x <= n {
        let mut count: i64 = 0;
        let mut i: usize = 0;

        while i < nums.len() {
            if nums[i] >= x {
                count += 1;
            }
            i += 1;
        }

        if count == x {
            return x;
        }

        x += 1;
    }

    -1
}
