pub fn sort_transformed_array(nums: &[i64], a: i64, b: i64, c: i64) -> Vec<i64> {
    let n = nums.len();
    let mut vals: Vec<i64> = Vec::new();

    let mut idx: usize = 0;
    while idx < n {
        let x = nums[idx];
        let y = a * x * x + b * x + c;
        vals.push(y);
        idx += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut min_idx: usize = i;
        let mut j: usize = i + 1;

        while j < n {
            if vals[j] < vals[min_idx] {
                min_idx = j;
            }
            j += 1;
        }

        if min_idx != i {
            let tmp = vals[i];
            vals[i] = vals[min_idx];
            vals[min_idx] = tmp;
        }

        i += 1;
    }

    vals
}
