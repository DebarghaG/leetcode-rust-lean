pub fn apply_operations(nums: &[i64]) -> Vec<i64> {
    let n = nums.len();
    let mut a: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        a.push(nums[i]);
        i += 1;
    }

    let mut i = 0usize;
    while i + 1 < n {
        if a[i] == a[i + 1] {
            a[i] = a[i] * 2;
            a[i + 1] = 0;
        }
        i += 1;
    }

    let mut out: Vec<i64> = Vec::new();

    let mut i = 0usize;
    while i < n {
        if a[i] != 0 {
            out.push(a[i]);
        }
        i += 1;
    }

    let mut zeros = out.len();
    while zeros < n {
        out.push(0);
        zeros += 1;
    }

    out
}
