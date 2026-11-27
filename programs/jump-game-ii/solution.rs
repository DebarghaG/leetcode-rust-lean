pub fn jump(nums: &[i64]) -> i64 {
    let n: usize = nums.len();
    if n <= 1 {
        return 0;
    }

    let mut jumps: i64 = 0;
    let mut current_end: usize = 0;
    let mut farthest: usize = 0;
    let mut i: usize = 0;

    while i + 1 < n {
        let reach: usize = i + nums[i] as usize;
        if reach > farthest {
            farthest = reach;
        }

        if i == current_end {
            jumps = jumps + 1;
            current_end = farthest;

            if current_end + 1 >= n {
                return jumps;
            }
        }

        i = i + 1;
    }

    jumps
}
