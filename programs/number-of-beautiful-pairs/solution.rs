fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn first_digit(mut x: i64) -> i64 {
    while x >= 10 {
        x = x / 10;
    }
    x
}

pub fn count_beautiful_pairs(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut ans: i64 = 0;
    let mut i: usize = 0;

    while i < n {
        let fd = first_digit(nums[i]);
        let mut j: usize = i + 1;

        while j < n {
            let ld = nums[j] % 10;
            if gcd(fd, ld) == 1 {
                ans += 1;
            }
            j += 1;
        }

        i += 1;
    }

    ans
}
