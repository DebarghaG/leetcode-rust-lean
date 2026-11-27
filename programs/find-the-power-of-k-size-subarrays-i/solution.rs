pub fn results_array(nums: &[i64], k: i64) -> Vec<i64> {
    let n = nums.len();
    let kk = k as usize;
    let mut out: Vec<i64> = Vec::new();

    if kk == 0 {
        return out;
    }

    let mut start: usize = 0;
    while start + kk <= n {
        let mut ok: bool = true;
        let mut j: usize = start + 1;
        let end: usize = start + kk;

        while j < end {
            if nums[j] != nums[j - 1] + 1 {
                ok = false;
            }
            j += 1;
        }

        if ok {
            out.push(nums[end - 1]);
        } else {
            out.push(-1);
        }

        start += 1;
    }

    out
}
