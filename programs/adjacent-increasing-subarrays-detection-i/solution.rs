pub fn has_increasing_subarrays(nums: &[i64], k: i64) -> bool {
    let n = nums.len();
    let kk = k as usize;

    if kk == 0 {
        return false;
    }

    let mut a: usize = 0;

    while a + 2 * kk <= n {
        let mut first_ok = true;
        let mut i: usize = 0;
        while i + 1 < kk {
            if nums[a + i] >= nums[a + i + 1] {
                first_ok = false;
            }
            i += 1;
        }

        let mut second_ok = true;
        let mut j: usize = 0;
        while j + 1 < kk {
            if nums[a + kk + j] >= nums[a + kk + j + 1] {
                second_ok = false;
            }
            j += 1;
        }

        if first_ok && second_ok {
            return true;
        }

        a += 1;
    }

    false
}
