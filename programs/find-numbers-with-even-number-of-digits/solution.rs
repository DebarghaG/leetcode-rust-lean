pub fn find_numbers(nums: &[i64]) -> i64 {
    let mut count: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        let mut x: i64 = nums[i];
        let mut digits: i64 = 0;

        while x > 0 {
            digits += 1;
            x = x / 10;
        }

        if digits % 2 == 0 {
            count += 1;
        }

        i += 1;
    }

    count
}
