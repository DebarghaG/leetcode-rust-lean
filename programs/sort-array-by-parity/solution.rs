pub fn sort_array_by_parity(nums: &[i64]) -> Vec<i64> {
    let mut res: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < nums.len() {
        res.push(nums[k]);
        k += 1;
    }

    let n: usize = nums.len();
    if n == 0 {
        return res;
    }

    let mut i: usize = 0;
    let mut j: usize = n - 1;

    while i < j {
        if res[i] % 2 == 0 {
            i += 1;
        } else if res[j] % 2 != 0 {
            j -= 1;
        } else {
            let tmp: i64 = res[i];
            res[i] = res[j];
            res[j] = tmp;
            i += 1;
            j -= 1;
        }
    }

    res
}
