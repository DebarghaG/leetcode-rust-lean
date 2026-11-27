pub fn max_strength(nums: &[i64]) -> i64 {
    let n: usize = nums.len();

    let mut total: usize = 1;
    let mut k: usize = 0;
    while k < n {
        total = total * 2;
        k += 1;
    }

    let mut best: i64 = nums[0];
    let mut mask: usize = 0;

    while mask < total {
        let mut x: usize = mask;
        let mut product: i64 = 1;
        let mut selected: bool = false;
        let mut i: usize = 0;

        while i < n {
            if x % 2 == 1 {
                product = product * nums[i];
                selected = true;
            }
            x = x / 2;
            i += 1;
        }

        if selected && product > best {
            best = product;
        }

        mask += 1;
    }

    best
}
