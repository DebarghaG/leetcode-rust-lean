pub fn decompress_rl_elist(nums: &[i64]) -> Vec<i64> {
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i + 1 < nums.len() {
        let freq = nums[i];
        let val = nums[i + 1];

        let mut k: i64 = 0;
        while k < freq {
            out.push(val);
            k += 1;
        }

        i += 2;
    }

    out
}
