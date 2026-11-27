pub fn maximum_value_sum(nums: &[i64], k: i64, edges: &[Vec<i64>]) -> i64 {
    let n = nums.len();
    let mut total: i64 = 0;
    let mut flipped: usize = 0;
    let mut min_loss: i64 = 1000000000000000000;
    let mut i: usize = 0;

    while i < n {
        let a = nums[i];
        let b = a ^ k;

        if b > a {
            total += b;
            flipped += 1;

            let loss = b - a;
            if loss < min_loss {
                min_loss = loss;
            }
        } else {
            total += a;

            let loss = a - b;
            if loss < min_loss {
                min_loss = loss;
            }
        }

        i += 1;
    }

    if flipped % 2 == 1 {
        total -= min_loss;
    }

    total
}
