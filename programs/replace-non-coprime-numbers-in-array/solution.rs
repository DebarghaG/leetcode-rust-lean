fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

pub fn replace_non_coprimes(nums: &[i64]) -> Vec<i64> {
    let mut stack: Vec<i64> = Vec::new();
    let mut i: usize = 0;

    while i < nums.len() {
        let mut x: i64 = nums[i];

        loop {
            let n = stack.len();
            if n == 0 {
                break;
            }

            let y = stack[n - 1];
            let g = gcd(x, y);

            if g <= 1 {
                break;
            }

            let _ = stack.pop();
            x = (x / g) * y;
        }

        stack.push(x);
        i += 1;
    }

    stack
}
