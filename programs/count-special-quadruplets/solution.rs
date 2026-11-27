pub fn count_quadruplets(nums: &[i64]) -> i64 {
    let n = nums.len();
    let mut count: i64 = 0;

    let mut a: usize = 0;
    while a < n {
        let mut b: usize = a + 1;
        while b < n {
            let mut c: usize = b + 1;
            while c < n {
                let mut d: usize = c + 1;
                while d < n {
                    if nums[a] + nums[b] + nums[c] == nums[d] {
                        count += 1;
                    }
                    d += 1;
                }
                c += 1;
            }
            b += 1;
        }
        a += 1;
    }

    count
}
