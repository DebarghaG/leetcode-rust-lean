pub fn k_length_apart(nums: &[i64], k: i64) -> bool {
    let n: usize = nums.len();
    let mut i: usize = 0;
    let mut gap: i64 = k; // gap since last 1; start at k => "satisfied" before first 1
    let mut ok: bool = true;

    while i < n {
        if nums[i] == 1 {
            if gap < k {
                ok = false;
            }
            gap = 0;
        } else {
            gap = gap + 1;
        }
        i = i + 1;
    }

    ok
}
