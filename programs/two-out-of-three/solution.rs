fn contains(xs: &[i64], target: i64) -> bool {
    let mut i: usize = 0;
    while i < xs.len() {
        if xs[i] == target {
            return true;
        }
        i += 1;
    }
    false
}

pub fn two_out_of_three(nums1: &[i64], nums2: &[i64], nums3: &[i64]) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();

    let mut value: i64 = 1;
    while value <= 100 {
        let mut count: i64 = 0;

        if contains(nums1, value) {
            count += 1;
        }
        if contains(nums2, value) {
            count += 1;
        }
        if contains(nums3, value) {
            count += 1;
        }

        if count >= 2 {
            result.push(value);
        }

        value += 1;
    }

    result
}
