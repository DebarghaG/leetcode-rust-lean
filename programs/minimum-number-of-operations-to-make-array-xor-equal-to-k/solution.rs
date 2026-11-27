pub fn min_operations(nums: &[i64], k: i64) -> i64 {
    let mut x: i64 = 0;
    let mut i: usize = 0;

    while i < nums.len() {
        x = x ^ nums[i];
        i += 1;
    }

    let mut v: i64 = x ^ k;
    let mut ans: i64 = 0;

    while v > 0 {
        if v % 2 == 1 {
            ans += 1;
        }
        v = v / 2;
    }

    ans
}
