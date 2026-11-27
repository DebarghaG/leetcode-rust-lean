pub fn find_gcd(nums: &[i64]) -> i64 {
    let mut i: usize = 0;
    let mut smallest: i64 = nums[0];
    let mut largest: i64 = nums[0];

    while i < nums.len() {
        let x: i64 = nums[i];
        if x < smallest {
            smallest = x;
        }
        if x > largest {
            largest = x;
        }
        i += 1;
    }

    gcd(smallest, largest)
}

fn gcd(a: i64, b: i64) -> i64 {
    let mut x: i64 = a;
    let mut y: i64 = b;

    while y != 0 {
        let r: i64 = x % y;
        x = y;
        y = r;
    }

    x
}
