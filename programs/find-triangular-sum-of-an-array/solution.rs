pub fn triangular_sum(nums: &[i64]) -> i64 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }

    let mut cur: Vec<i64> = Vec::new();
    let mut i = 0;
    while i < n {
        cur.push(nums[i]);
        i += 1;
    }

    let mut len = n;
    while len > 1 {
        let mut j = 0;
        while j + 1 < len {
            cur[j] = (cur[j] + cur[j + 1]) % 10;
            j += 1;
        }
        len -= 1;
    }

    cur[0]
}
