pub fn num_of_pairs(nums: &[Vec<u8>], target: &[u8]) -> i64 {
    let n = nums.len();
    let target_len = target.len();
    let mut ans: i64 = 0;

    let mut i = 0;
    while i < n {
        let a = &nums[i];
        let a_len = a.len();

        let mut j = 0;
        while j < n {
            if i != j {
                let b = &nums[j];
                let b_len = b.len();

                if a_len + b_len == target_len {
                    let mut ok = true;

                    let mut k = 0;
                    while ok && k < a_len {
                        if a[k] != target[k] {
                            ok = false;
                        }
                        k += 1;
                    }

                    let mut m = 0;
                    while ok && m < b_len {
                        if b[m] != target[a_len + m] {
                            ok = false;
                        }
                        m += 1;
                    }

                    if ok {
                        ans += 1;
                    }
                }
            }
            j += 1;
        }
        i += 1;
    }

    ans
}
