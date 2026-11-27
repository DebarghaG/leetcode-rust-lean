pub fn transform_array(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut odds: usize = 0;
    let mut i: usize = 0;
    while i < n {
        if nums[i] % 2 != 0 {
            odds += 1;
        }
        i += 1;
    }

    let evens = n - odds;
    let mut out: Vec<i64> = Vec::new();

    let mut j: usize = 0;
    while j < evens {
        out.push(0);
        j += 1;
    }

    let mut k: usize = 0;
    while k < odds {
        out.push(1);
        k += 1;
    }

    out
}
