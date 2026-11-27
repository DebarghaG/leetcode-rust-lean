pub fn remove_duplicates(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    let mut k: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        // Find the end of the current run of equal elements.
        let mut j: usize = i;
        while j < n && nums[j] == nums[i] {
            j += 1;
        }
        let run: i64 = (j - i) as i64;
        if run <= 2 {
            k += run;
        } else {
            k += 2;
        }
        i = j;
    }
    k
}
