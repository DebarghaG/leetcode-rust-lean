pub fn number_of_subarrays(nums: &[i64]) -> i64 {
    let n = nums.len();

    let mut vals: Vec<i64> = Vec::new();
    let mut counts: Vec<i64> = Vec::new();
    let mut top: usize = 0;
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let x = nums[i];

        while top > 0 && vals[top - 1] < x {
            top = top - 1;
        }

        if top > 0 && vals[top - 1] == x {
            counts[top - 1] = counts[top - 1] + 1;
        } else {
            if top < vals.len() {
                vals[top] = x;
                counts[top] = 1;
            } else {
                vals.push(x);
                counts.push(1);
            }
            top = top + 1;
        }

        ans = ans + counts[top - 1];
        i = i + 1;
    }

    ans
}
