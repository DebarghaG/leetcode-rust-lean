pub fn tuple_same_product(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut products: Vec<i64> = Vec::new();

    let mut i = 0;
    while i < n {
        let mut j = i + 1;
        while j < n {
            products.push(nums[i] * nums[j]);
            j += 1;
        }
        i += 1;
    }

    products.sort();

    let mut ans: i64 = 0;
    let mut p = 0;
    while p < products.len() {
        let cur = products[p];
        let mut q = p + 1;
        while q < products.len() && products[q] == cur {
            q += 1;
        }

        let cnt = (q - p) as i64;
        ans = ans + cnt * (cnt - 1) * 4;
        p = q;
    }

    ans
}
